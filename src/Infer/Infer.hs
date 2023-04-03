{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
module Infer.Infer (Constraint(..), runInfer, runInferIO
                  , InferM, InferRes(..), Collect(..)
                  , Signature) where

import Common
import Syntax
import Type
import qualified Data.Map as Map
import qualified Data.Set.Monad as Set 
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.Except

data Constraint
  = CPureTLE PureType PureType     -- a pure type is smaller than another
  | CDirtyTLE DirtyType DirtyType  -- a dirty type is smaller than another
  | CDirtLE Dirt Dirt              -- a dirt is smaller than another
  deriving (Eq, Ord)

instance Show Constraint where
  show (CPureTLE p1 p2) = show p1 ++ " <= " ++ show p2
  show (CDirtyTLE d1 d2) = show d1 ++ " <= " ++ show d2
  show (CDirtLE d1 d2) = show d1 ++ " <= " ++ show d2

type ConsSet = Set.Set Constraint

-- the type scheme, which includes a set of constraints on it
data Scheme = Forall VarSet PureType ConsSet

-- the normal typing context
type MonoCtx = Map.Map Id PureType
-- the polymorphic context, which is the map of variables to type schemes
type PolyCtx = Map.Map Id Scheme
data Context = Context MonoCtx PolyCtx
emptyCtx = Context Map.empty Map.empty

data InferRes r = Res 
                    VarSet  -- the fresh variables introduced
                    r       -- the result type inferred
                    ConsSet -- the constraints generated

instance Show a => Show (InferRes a) where
  show (Res f a c) = "Res: "
                   ++ "freeVars: " ++ show f 
                   ++ ", \nresultType: " ++  show a 
                   ++ ", \nconstraints: " ++ show c

-- map from an optag to a pair of input & output type
type Signature = Map.Map OpTag (PureType, PureType)

class (MonadState [Id] m        -- a stream of global fresh names
     , MonadReader Signature m  -- the input effect signatures
     , MonadWriter String m     -- logging
     , MonadError String m      -- error messages
     ) => InferMonad m where
     -- TODO: wrap the String here to an error data type
  getFreshName :: m Id
  getFreshName = do 
    xs <- get
    put (tail xs)
    return (head xs)

  lookupSignature :: OpTag -> m (PureType, PureType)
  lookupSignature op = do
    signature <- ask
    case Map.lookup op signature of
      Just x -> return x
      Nothing -> throwError $ "undefined operation: " ++ show op

class Collect a r | a -> r where
-- the algorithm to collect constraints from the AST
-- derived from the inference rules
  collectConstraints :: InferMonad m => Context -> a -> m (InferRes r)

instance Collect Expr PureType where
  collectConstraints (Context mctx pctx) e = case e of
    -- Cstr-Var & Cstr PolyVar
    Var x -> case (Map.lookup x mctx, Map.lookup x pctx) of
               (Just pt, Nothing) -> return (Res Set.empty pt Set.empty)
               -- See: Inferring Algeff p. 19
               (Nothing, Just (Forall f a cons)) -> do
                 -- rename bound params F and obtain a fresh copy as each use
                 nn's <- forM (Set.toList f) $ \n -> do 
                           n' <- getFreshName
                           return (n, n')
                 let s = Map.fromList nn's
                     f' = Set.fromList (snd <$> nn's)
                     a' = apply s a
                 return (Res f' a' cons)
               (Nothing, Nothing) -> throwError $ "undefined variable: " ++ show x
               _ -> error "internal error: mctx & pctx should be disjoint"
    -- literals
    Lit (LBool _) -> return (Res Set.empty typeBool Set.empty)
    Lit (LInt _) -> return (Res Set.empty typeInt Set.empty)
    Lit LUnit -> return (Res Set.empty typeTop Set.empty) 
    -- Cstr-Fun
    Abs x c -> do
      _a <- getFreshName
      let a = TVar (TV _a)
      Res f _c cons <- collectConstraints (Context (mctx ?: (x, a)) pctx) c
      return (Res (Set.insert _a f) (TFunc a _c) cons)
    -- Cstr-Hand
    -- TODO: Can `PureType` in the constructor be removed?
    Handler x _ cv ocs' -> do
      _alIn <- getFreshName  -- the incoming type
      _alOut <- getFreshName -- the outgoing type
      dIn <- getFreshName    -- the rest of incoming dirt
      dOut <- getFreshName   -- the rest of outgoing dirt
      let ocs = traverseOcs ocs'
          ops = Set.fromList $ [op | (op, _, _, _) <- ocs] -- all the operations handled
          alIn = typeVar _alIn
          alOut = typeVar _alOut
          -- the handler type is _C => _D
          _C = DirtyType alIn (Dirt ops (DV dIn))
          _D = DirtyType alOut (Dirt Set.empty (DV dOut))
      -- infer the value case
      Res fv _Dv consv <- collectConstraints (Context (mctx ?: (x, alIn)) pctx) cv
      -- then traverse and check each opcase, the `Psi`
      ress <- forM ocs $ \(opi, xi, ki, ci) -> do
                (_A, _B) <- lookupSignature opi
                -- TODO: check why it's no pctx here
                collectConstraints (Context (mctx ?: (xi, _A) ?: (ki, TFunc _B _D)) Map.empty) ci
      -- collect all constraints `consRes`
      let consRes = consv 
                 \/ Set.unions [c | Res _ _ c <- ress]
                 \/ Set.fromList (CDirtyTLE _Dv _D : 
                                 [CDirtyTLE _Di _D | Res _ _Di _ <- ress])
                 -- TODO: check this dirt? Is this correct?
                 \/ Set.singleton (CDirtLE (Dirt Set.empty (DV dIn)) (Dirt Set.empty (DV dOut)))
      -- collect the set f, `fRes`
          fRes = fv 
              \/ Set.unions [fi | Res fi _ _ <- ress]
              \/ Set.fromList [_alIn, _alOut, dIn, dOut]
      return (Res fRes (THandler _C _D) consRes)
    -- TODO:
    Arith e -> undefined
    ADT e -> undefined
    where
      typeVar t = TVar (TV t)

instance Collect Computation DirtyType where
  collectConstraints ctx@(Context mctx pctx) _c = case _c of
    -- Cstr-Val
    Ret e -> do
      d <- getFreshName
      Res f a cons <- collectConstraints ctx e
      let dv = dirtVar d
      return (Res (Set.insert d f) (DirtyType a dv) cons)
    -- Cstr-App
    App e1 e2 -> do
      tell $ "\n\nin app: " ++ show _c ++ "\n"
      Res f1 a1 cons1 <- collectConstraints ctx e1
      Res f2 a2 cons2 <- collectConstraints ctx e2
      _al <- getFreshName
      d <- getFreshName
      let dv = dirtVar d
          al = typeVar _al
          resultTy = DirtyType al dv
          cons' = Set.insert (CPureTLE a1 (TFunc a2 resultTy)) cons1 \/ cons2 
          f' = f1 \/ f2 \/ Set.fromList [_al, d]
      tell $ show (Res f' resultTy cons')
      return (Res f' resultTy cons')
    -- Cstr-IfThenElse
    If e cm1 cm2 -> do
      Res f a cons <- collectConstraints ctx e
      Res f1 c1 cons1 <- collectConstraints ctx cm1
      Res f2 c2 cons2 <- collectConstraints ctx cm2
      _al <- getFreshName
      d <- getFreshName
      let dv = dirtVar d
          al = typeVar _al
          resultTy = DirtyType al dv
          cons' = cons \/ cons1 \/ cons2 \/ Set.fromList
                    [ CPureTLE a typeBool
                    , CDirtyTLE c1 resultTy
                    , CDirtyTLE c2 resultTy]
          f' = f \/ f1 \/ f2 \/ Set.fromList [_al, d]
      return (Res f' resultTy cons')
    -- Cstr-Op, modified
    OpCall op e -> do
      (aop, bop) <- lookupSignature op
      Res f a cons <- collectConstraints ctx e
      d <- getFreshName
      let resultTy = DirtyType bop (Dirt (Set.singleton op) (DV d))
          cons' = cons \/ Set.singleton (CPureTLE a aop)
          f' = Set.insert d f
      return (Res f' resultTy cons')
    -- Cstr-With
    WithHandle e cm -> do
      Res f1 a cons1 <- collectConstraints ctx e
      Res f2 c cons2 <- collectConstraints ctx cm
      _al <- getFreshName
      d <- getFreshName
      let dv = dirtVar d
          al = typeVar _al
          resultTy = DirtyType al dv
          cons' = cons1 \/ cons2 
               \/ Set.singleton (CPureTLE a (THandler c resultTy))
          f' = f1 \/ f2 \/ Set.fromList [_al, d]
      return (Res f' resultTy cons')
    -- Cstr-Absurd
    Absurd _ e -> do
      Res f a cons <- collectConstraints ctx e
      _al <- getFreshName
      d <- getFreshName
      let dv = dirtVar d
          al = typeVar _al
          resultTy = DirtyType al dv
          cons' = Set.insert (CPureTLE a typeBottom) cons
          f' = f \/ Set.fromList [_al, d]
      return (Res f' resultTy cons')
    -- CStr-LetVar
    Let x e cm -> do
      tt@(Res f1 a cons1) <- collectConstraints ctx e
      tell $ "\n\nin let:\n"
      tell $ show tt
      let ctx' = Context mctx (pctx ?: (x, Forall f1 a cons1))
      Res f2 c cons2 <- collectConstraints ctx' cm
      return (Res f2 c cons2)
    -- Cstr-Let
    Do x c1 c2 -> do
      Res f1 (DirtyType a d1) cons1 <- collectConstraints ctx c1
      _al <- getFreshName
      d <- getFreshName
      let dv = dirtVar d
          al = typeVar _al
          ctx' = Context (mctx ?: (x, al)) pctx
      Res f2 (DirtyType b d2) cons2 <- collectConstraints ctx' c2
      let resultTy = DirtyType b dv
          cons' = cons1 \/ cons2 \/ Set.fromList 
                    [ CPureTLE a al
                    , CDirtLE d1 dv
                    , CDirtLE d2 dv]
          f' = f1 \/ f2 \/ Set.fromList [_al, d]
      return (Res f' resultTy cons')
    -- Cstr-LetRec
    DoRec f x c1 c2 -> do
      _al1 <- getFreshName
      _al2 <- getFreshName
      d <- getFreshName
      let dv = dirtVar d
          al1 = typeVar _al1
          al2 = typeVar _al2
          al2d = DirtyType al2 dv
          mctx_f = mctx ?: (f, TFunc al1 al2d)
          mctx_fx = mctx_f ?: (x, al1)
      Res f1 dtc cons1 <- collectConstraints (Context mctx_fx pctx) c1
      Res f2 dtd cons2 <- collectConstraints (Context mctx_f pctx) c2
      let cons' = cons1 \/ cons2 \/ Set.singleton (CDirtyTLE dtc al2d)
          f' = f1 \/ f2 \/ Set.fromList [_al1, _al2, d]
      return (Res f' dtd cons')
    -- TODO:
    Case e cs -> undefined
    where
      dirtVar d = Dirt Set.empty (DV d)
      typeVar t = TVar (TV t)

-- instantiate
type InferM = ExceptT String (ReaderT Signature (WriterT String (State [Id]))) 
instance InferMonad InferM 

runInfer :: Collect a r => a
                        -> Signature
                        -> (Either String (InferRes r), [Char])
runInfer e signature = 
  evalState (runWriterT (runReaderT 
    (runExceptT (collectConstraints emptyCtx e)) signature)) letters

runInferIO :: (Show r, Collect p r) => p -> Signature 
                                    -> IO (Either String (InferRes r))
runInferIO e signature = do
    let (res, info) = runInfer e signature
    case res of
      Right r -> putStrLn $ "the infered result is: " ++ show r
      Left err -> putStrLn $ "error in typechecking: " ++ err
    putStrLn "-------------------"
    yellow $ "log: " ++ info
    return res

