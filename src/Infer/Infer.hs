{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
module Infer.Infer 
  ( Constraint(..), runInfer, runInferIO
  , InferM, InferRes(..), Collect(..)
  , Signature(..), emptySig
  ) where

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
                   { freshVars :: VarSet      -- the fresh variables introduced
                   , resType :: r            -- the result type inferred
                   , constraints :: ConsSet } -- the constraints generated

instance Show a => Show (InferRes a) where
  show (Res f a c) = "Res: "
                   ++ "freeVars: " ++ show f 
                   ++ ", \nresultType: " ++  show a 
                   ++ ", \nconstraints: " ++ show c

-- map from an optag to a pair of input & output type
data Signature = Signature 
                  { consSig :: ConsSignature 
                  , opSig :: OpSignature }

emptySig :: Signature
emptySig = Signature Map.empty Map.empty

class ( MonadState [Id] m        -- a stream of global fresh names
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

  lookupOpSignature :: OpTag -> m (PureType, PureType)
  lookupOpSignature op = do
    signature <- asks opSig
    case Map.lookup op signature of
      Just x -> return x
      Nothing -> throwError $ "undefined operation: " ++ show op

  lookupConsSignature :: ConsName -> m TypeEntry
  lookupConsSignature cons = do
    signature <- asks consSig
    case Map.lookup cons signature of
      Just x -> return x
      Nothing -> throwError $ "undefined constructor: " ++ show cons
  
class Collect a r | a -> r where
-- the algorithm to collect constraints from the AST
-- derived from the inference rules
  collectConstraints :: InferMonad m => Context -> a -> m (InferRes r)

instance Collect Expr PureType where
  -- Cstr-Var & Cstr PolyVar
  collectConstraints (Context mctx pctx) (Var x) =
    case (Map.lookup x mctx, Map.lookup x pctx) of
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
  collectConstraints _ (Lit l) = do 
      let t = case l of
                LBool _ -> typeBool
                LInt _ -> typeInt
                LUnit -> typeTop
      return (Res Set.empty t Set.empty)
  -- Cstr-Fun
  collectConstraints (Context mctx pctx) (Abs x c) = do
      _a <- getFreshName
      let a = TVar (TV _a)
      Res f _c cons <- collectConstraints (Context (mctx ?: (x, a)) pctx) c
      return (Res (Set.insert _a f) (TFunc a _c) cons)
  -- Cstr-Hand
  -- TODO: Can `PureType` in the constructor be removed?
  collectConstraints (Context mctx pctx) (Handler x _ cv ocs') = do
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
          _D = DirtyType alOut (dirtVar dOut)
      -- infer the value case
      Res fv _Dv consv <- collectConstraints (Context (mctx ?: (x, alIn)) pctx) cv
      -- then traverse and check each opcase, the `Psi`
      ress <- forM ocs $ \(opi, xi, ki, ci) -> do
                (_A, _B) <- lookupOpSignature opi
                -- TODO: check why it's no pctx here
                collectConstraints (Context (mctx ?: (xi, _A) ?: (ki, TFunc _B _D)) Map.empty) ci
      -- collect all constraints `consRes`
      let consRes = consv 
                 \/ Set.unions (constraints <$> ress)
                 \/ Set.fromList (CDirtyTLE _Dv _D : 
                                 [CDirtyTLE _Di _D | _Di <- resType <$> ress])
                 -- TODO: check this dirt? Is this correct?
                 \/ Set.singleton (CDirtLE (dirtVar dIn) (dirtVar dOut))
      -- collect the set f, `fRes`
          fRes = fv 
              \/ Set.unions (freshVars <$> ress)
              \/ Set.fromList [_alIn, _alOut, dIn, dOut]
      return (Res fRes (THandler _C _D) consRes)
  -- Arith
  collectConstraints ctx (Arith (BOp op e1 e2)) 
    | op `elem` [Add, Sub, Mul, Div] = bopCons typeInt typeInt
    | op `elem` [Eq, Lt, Gt] = bopCons typeInt typeBool
    | op `elem` [And, Or] = bopCons typeBool typeBool
    | otherwise = undefined
    where bopCons t1 t2 = do
            Res f1 a1 cons1 <- collectConstraints ctx e1
            Res f2 a2 cons2 <- collectConstraints ctx e2
            let f' = f1 \/ f2
                cons' = cons1 \/ cons2 
                     \/ Set.fromList [ CPureTLE a1 t1
                                     , CPureTLE a2 t1 ]
            return (Res f' t2 cons')
  collectConstraints ctx (Arith (UOp op e)) 
    | op == Neg = uopCons typeInt
    | op == Not = uopCons typeBool
    | otherwise = undefined
    where uopCons t = do
            Res f a cons <- collectConstraints ctx e
            return (Res f t (Set.insert (CPureTLE a t) cons))
            
  collectConstraints ctx (Cons cons xs) = do
    t <- lookupConsSignature cons
    if arity t /= length xs 
    then throwError $ "the constructor " ++ show cons ++ "should have "
                ++ show (arity t) ++ " arguments, but has been given " 
                ++ show (length xs)
    else do
      ress <- traverse (collectConstraints ctx) xs
      let f' = Set.unions (freshVars <$> ress)
          c' = Set.unions (constraints <$> ress)
            \/ Set.fromList [CPureTLE ai ti  
                              | (ai, ti) <- zip (resType <$> ress) (paramType t)]
      return (Res f' (retType t) c')

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
      (aop, bop) <- lookupOpSignature op
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
 
    -- CStr-Case
    Case e cs -> do
      Res f a cstr <- collectConstraints ctx e
      let doPattern :: InferMonad m => Pattern -> PureType -> m (MonoCtx, [Constraint])
          doPattern (PVar x) t = return (Map.singleton x t, [])
          doPattern PWild _ = return (Map.empty, [])
          doPattern (PCons cons ps) t' = do
            t <- lookupConsSignature cons
            if arity t /= length ps 
            then throwError $ "the constructor " ++ show cons ++ "should have "
                        ++ show (arity t) ++ " arguments, but has been given " 
                        ++ show (length ps)
            else do
              (mctxs, cstrss) <- unzip <$> traverse (uncurry doPattern) (zip ps (paramType t))
              return (Map.unions mctxs, CPureTLE t' (retType t) : join cstrss)

      ress <- forM cs $ \(p, ci) -> do
                (mctx', cstrs) <- doPattern p a 
                Res f' a' c' <- collectConstraints (Context (Map.union mctx' mctx) pctx) ci
                return (Res f' a' (c' \/ Set.fromList cstrs))
      _al <- getFreshName
      d <- getFreshName
      let resultTy = DirtyType (typeVar _al) (dirtVar d)
          f' = f \/ Set.unions (freshVars <$> ress)
          cstr' = cstr \/ Set.unions (constraints <$> ress)
               \/ Set.fromList [CDirtyTLE _ci resultTy
                                  | _ci <- resType <$> ress]
      return (Res f' resultTy cstr')

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
    yellow $ "infer log: " ++ info
    return res

