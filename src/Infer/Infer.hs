{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
module Infer.Infer 
  ( Constraint(..), runInfer, runInferIO
  , InferMonad, InferM, InferRes(..), Collect(..)
  , InferErrorMonad(..), InferLogMonad(..)
  , Context(..), MonoCtx, PolyCtx, Scheme(..)
  , Signature(..), emptySig
  , InferError
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

instance Rename Constraint where
  apply s (CPureTLE p1 p2) = CPureTLE (apply s p1) (apply s p2)
  apply s (CDirtyTLE d1 d2) = CDirtyTLE (apply s d1) (apply s d2)
  apply s (CDirtLE d1 d2) = CDirtLE (apply s d1) (apply s d2)

  free = undefined

instance Rename ConsSet where
  apply s = Set.map (apply s)

  free = undefined

-- the type scheme, which includes a set of constraints on it
-- it also represents the result of an inference
data Scheme = Forall VarSet PureType ConsSet

instance Rename Scheme where
  normalize (Forall _ t c) = let s = evalState (normalize' t) letters
                                 t' = apply s t
                                 c' = apply s c
                                 f' = free t'
                              in Forall f' t' c'

instance Show Scheme where
  show (Forall f p c) = -- params ++ 
                        show p ++ cons
    where params = if Set.null f then "" 
                   else "forall" ++ concat (Set.map (" "++) f) ++ "." 
          cons = if Set.null c then ""
                 else " | " ++ show (Set.toList c)

-- the normal typing context
type MonoCtx = Map.Map Id PureType
-- the polymorphic context, which is the mapping of variables to type schemes
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

data InferError = UndefinedOperation OpTag
                | UndefinedConstructor ConsName
                | UndefinedVariable Id
                | ConstructorArgMismatch ConsName Int Int

instance Show InferError where
  show (UndefinedOperation op) = "undefined operation: " ++ show op
  show (UndefinedConstructor cons) = "undefined constructor: " ++ show cons
  show (UndefinedVariable x) = "undefined variable: " ++ show x
  show (ConstructorArgMismatch cons ex ac) = 
      "the constructor " ++ show cons ++ "should have "
      ++ show ex ++ " arguments, but has been given " 
      ++ show ac

class ( MonadState [Id] m        -- a stream of global fresh names
      , MonadReader Signature m  -- the input effect signatures
      , MonadWriter String m     -- logging
      , MonadError InferError m      -- error messages
      ) => InferMonad m where
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
      Nothing -> throwError $ UndefinedOperation op

  lookupConsSignature :: ConsName -> m TypeEntry
  lookupConsSignature cons = do
    signature <- asks consSig
    case Map.lookup cons signature of
      Just x -> return x
      Nothing -> throwError $ UndefinedConstructor cons
  
class Collect a r | a -> r where
-- the algorithm to collect constraints from the AST
-- derived from the inference rules
  collectConstraints :: InferMonad m => Context -> a -> m (InferRes r)

instance Collect Expr PureType where
  -- Cstr-Var & Cstr PolyVar
  collectConstraints (Context mctx pctx) (Var x) =
    case (Map.lookup x mctx, Map.lookup x pctx) of
      (Just pt, Nothing) -> 
        tell (show pt) >>
        return (Res Set.empty pt Set.empty)
      -- See: Inferring Algeff p. 19
      (Nothing, Just (Forall f a cstr)) -> do
        -- rename bound params F and obtain a fresh copy as each use
        nn's <- forM (Set.toList f) $ \n -> do 
                  n' <- getFreshName
                  return (n, n')
        let s = Map.fromList nn's
            f' = Set.fromList (snd <$> nn's)
            a' = apply s a
            -- substitute the captured constraints as well
            cstr' = apply s cstr
        return (Res f' a' cstr')
      (Nothing, Nothing) -> throwError $ UndefinedVariable x
      _ -> error $ "internal error: mctx & pctx should be disjoint: " 
                ++ show x
  -- literals
  collectConstraints _ (Lit l) = do 
      let t = case l of
                LBool _ -> typeBool
                LInt _ -> typeInt
                LUnit -> typeTop
      return (Res Set.empty t Set.empty)
  -- Cstr-Fun
  collectConstraints (Context mctx pctx) (Abs x xs c) = do
      _a <- getFreshName
      let a = typeVar _a
      (mctx', f', hole) <- foldM f (mctx ?: (x, a), Set.empty, id) xs
      Res _f _c cstr <- collectConstraints (Context mctx' pctx) c
      return (Res (Set.insert _a _f \/ f') (TFunc a (hole _c)) cstr)
    where
      f :: InferMonad m 
        => (MonoCtx, VarSet, DirtyType -> DirtyType) 
        -> Id
        -> m (MonoCtx, VarSet, DirtyType -> DirtyType)
      f (lctx, lf, hole) x' = do
        _a <- getFreshName
        d <- getFreshName
        let a = typeVar _a
            dv = dirtVar d
            resultTy _c = DirtyType (TFunc a _c) dv
        return (lctx ?: (x', a), lf \/ Set.fromList [_a, d], hole . resultTy)

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
      Res fv _Dv cstrv <- collectConstraints (Context (mctx ?: (x, alIn)) pctx) cv
      -- then traverse and check each opcase, the `Psi`
      ress <- forM ocs $ \(opi, xi, ki, ci) -> do
                (_A, _B) <- lookupOpSignature opi
                -- TODO: check why it's no pctx here
                collectConstraints (Context (mctx ?: (xi, _A) ?: (ki, TFunc _B _D)) Map.empty) ci
      -- collect all constraints `cstrRes`
      let cstrRes = cstrv 
                 \/ Set.unions (constraints <$> ress)
                 \/ Set.fromList (CDirtyTLE _Dv _D : 
                                 [CDirtyTLE _Di _D | _Di <- resType <$> ress])
                 -- TODO: check this dirt? Is this correct?
                 \/ Set.singleton (CDirtLE (dirtVar dIn) (dirtVar dOut))
      -- collect the set f, `fRes`
          fRes = fv 
              \/ Set.unions (freshVars <$> ress)
              \/ Set.fromList [_alIn, _alOut, dIn, dOut]
      return (Res fRes (THandler _C _D) cstrRes)
  -- Arith
  collectConstraints ctx (Arith (BOp op e1 e2)) 
    | op `elem` [Add, Sub, Mul, Div] = bopCons typeInt typeInt
    | op `elem` [Eq, Lt, Gt] = bopCons typeInt typeBool
    | op `elem` [And, Or] = bopCons typeBool typeBool
    | otherwise = undefined
    where bopCons t1 t2 = do
            Res f1 a1 cstr1 <- collectConstraints ctx e1
            Res f2 a2 cstr2 <- collectConstraints ctx e2
            let f' = f1 \/ f2
                cstr' = cstr1 \/ cstr2 
                     \/ Set.fromList [ CPureTLE a1 t1
                                     , CPureTLE a2 t1 ]
            return (Res f' t2 cstr')
  collectConstraints ctx (Arith (UOp op e)) 
    | op == Neg = uopCons typeInt
    | op == Not = uopCons typeBool
    | otherwise = undefined
    where uopCons t = do
            Res f a cstr <- collectConstraints ctx e
            return (Res f t (Set.insert (CPureTLE a t) cstr))
            
  collectConstraints ctx (Cons cons xs) = do
    t <- lookupConsSignature cons
    if arity t /= length xs 
    then throwError $ ConstructorArgMismatch cons (arity t) (length xs)
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
      Res f a cstr <- collectConstraints ctx e
      let dv = dirtVar d
      return (Res (Set.insert d f) (DirtyType a dv) cstr)

    -- Cstr-App
    App fe e es -> do
      Res f1 a1 cstr1 <- collectConstraints ctx fe
      let 
          f :: InferMonad m 
                 => (DirtyType, ConsSet, VarSet)
                 -> Expr
                 -> m (DirtyType, ConsSet, VarSet)
          f (DirtyType a _, cstr, fs) e' = do
            -- for each argument expression
            -- get the previous type as the function type `a`
            -- the current argument type is `a'`
            Res f' a' cstr' <- collectConstraints ctx e'
            tell $ "\n  in app, now: " ++ show e' ++ " ;with function type: " ++ show a
            tell $ "\n  res: " ++ show (a', cstr')

            -- generate the new result type
            _al <- getFreshName
            d <- getFreshName
            let dv = dirtVar d
                al = typeVar _al
                resultTy = DirtyType al dv
                -- insert a new constraint: a <= a' -> al!dv
                cstr'' = cstr \/ cstr'
                      \/ Set.fromList [CPureTLE a (TFunc a' resultTy)] 
                f'' = fs \/ f' \/ Set.fromList [_al, d]
            -- return `al` as the next return type
            tell $ "\nres of this term: " ++ show (resultTy, cstr'', f'')
            return (resultTy, cstr'', f'')
      -- HACK: dummy argument here, the dirt won't be used in the fold
      (ra, rcstr, rf) <- foldM f (DirtyType a1 undefined, cstr1, f1) (e:es)
      return (Res rf ra rcstr)

    -- Cstr-IfThenElse
    If e cm1 cm2 -> do
      Res f a cstr <- collectConstraints ctx e
      Res f1 c1 cstr1 <- collectConstraints ctx cm1
      Res f2 c2 cstr2 <- collectConstraints ctx cm2
      _al <- getFreshName
      d <- getFreshName
      let dv = dirtVar d
          al = typeVar _al
          resultTy = DirtyType al dv
          cstr' = cstr \/ cstr1 \/ cstr2 \/ Set.fromList
                    [ CPureTLE a typeBool
                    , CDirtyTLE c1 resultTy
                    , CDirtyTLE c2 resultTy]
          f' = f \/ f1 \/ f2 \/ Set.fromList [_al, d]
      return (Res f' resultTy cstr')

    -- Cstr-Op, modified
    OpCall op e -> do
      (aop, bop) <- lookupOpSignature op
      Res f a cstr <- collectConstraints ctx e
      d <- getFreshName
      let resultTy = DirtyType bop (Dirt (Set.singleton op) (DV d))
          cstr' = cstr \/ Set.singleton (CPureTLE a aop)
          f' = Set.insert d f
      return (Res f' resultTy cstr')

    -- Cstr-With
    WithHandle e cm -> do
      Res f1 a cstr1 <- collectConstraints ctx e
      Res f2 c cstr2 <- collectConstraints ctx cm
      _al <- getFreshName
      d <- getFreshName
      let dv = dirtVar d
          al = typeVar _al
          resultTy = DirtyType al dv
          cstr' = cstr1 \/ cstr2 
               \/ Set.singleton (CPureTLE a (THandler c resultTy))
          f' = f1 \/ f2 \/ Set.fromList [_al, d]
      return (Res f' resultTy cstr')

    -- Cstr-Absurd
    Absurd _ e -> do
      Res f a cstr <- collectConstraints ctx e
      _al <- getFreshName
      d <- getFreshName
      let dv = dirtVar d
          al = typeVar _al
          resultTy = DirtyType al dv
          cstr' = Set.insert (CPureTLE a typeBottom) cstr
          f' = f \/ Set.fromList [_al, d]
      return (Res f' resultTy cstr')

    -- CStr-LetVar
    Let x e cm -> do
      tt@(Res f1 a cstr1) <- collectConstraints ctx e
      tell $ "\n\nin let:\n"
      tell $ show tt
      let ctx' = Context mctx (pctx ?: (x, Forall f1 a cstr1))
      Res f2 c cstr2 <- collectConstraints ctx' cm
      return (Res f2 c cstr2)

    -- Cstr-Let
    Do stmts ret -> do
      d <- getFreshName
      let dv = dirtVar d  -- the dirt of the whole computation
          -- process each statement
          f :: InferMonad m 
            => (Context, ConsSet, VarSet)
            -> DoStmt 
            -> m (Context, ConsSet, VarSet)
          f (lctx@(Context lmctx lpctx), lcstr, lf) stmt = case stmt of
            Bind x c -> do
              -- infer with last context
              Res f' (DirtyType a d1) cstr' <- collectConstraints lctx c
              _al <- getFreshName
              let al = typeVar _al
              let ctx' = Context (lmctx ?: (x, al)) lpctx
                  -- dirt of each subcomputation should be smaller than the whole dirt
                  cstr'' = lcstr \/ cstr' \/ Set.fromList [CPureTLE al a, CDirtLE d1 dv]
              -- tell "\n----------"
              -- tell $ "\ncurrent ctx: " ++ show lmctx
              -- tell $ "\ncurrent var: " ++ show (x, al)
              -- tell $ "\nnew ctx: " ++ show (lmctx ?: (x, al))
              return (ctx', cstr'', Set.insert _al f' \/ lf)
            DoLet x e -> do
              Res f' a' cstr' <- collectConstraints lctx e
              let ctx' = Context lmctx (lpctx ?: (x, Forall f' a' cstr'))
              -- only changes the poly context
              return (ctx', lcstr, lf)
            DoC c -> do
              Res f' (DirtyType _ d1) cstr' <- collectConstraints lctx c
              -- dirt of each subcomputation should be smaller than the whole dirt
              return (lctx, Set.insert (CDirtLE d1 dv) cstr' \/ lcstr, f' \/ lf)

      (lctx, lcstr, lf) <- foldM f (ctx, Set.empty, Set.empty) stmts
      -- infer with the collected context, get the result type
      Res fr (DirtyType b dr) cstr <- collectConstraints lctx ret
      let resultTy = DirtyType b dv
          cstr' = cstr \/ lcstr \/ Set.singleton (CDirtLE dr dv)
          f' = fr \/ lf \/ Set.singleton d
      return (Res f' resultTy cstr')

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
      Res f1 dtc cstr1 <- collectConstraints (Context mctx_fx pctx) c1
      Res f2 dtd cstr2 <- collectConstraints (Context mctx_f pctx) c2
      let cstr' = cstr1 \/ cstr2 \/ Set.singleton (CDirtyTLE dtc al2d)
          f' = f1 \/ f2 \/ Set.fromList [_al1, _al2, d]
      return (Res f' dtd cstr')
 
    -- CStr-Case
    Case e cs -> do
      Res f a cstr <- collectConstraints ctx e
      let doPattern :: InferMonad m => Pattern -> PureType -> m (MonoCtx, [Constraint])
          doPattern (PVar x) t = return (Map.singleton x t, [])
          doPattern PWild _ = return (Map.empty, [])
          doPattern (PCons cons ps) t' = do
            t <- lookupConsSignature cons
            if arity t /= length ps 
            then throwError $ ConstructorArgMismatch cons (arity t) (length ps)
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
type InferM = ExceptT InferError (ReaderT Signature (WriterT String (State [Id]))) 
instance InferMonad InferM 

class Monad m => InferLogMonad m where
  inferLog :: String -> m ()

class Monad m => InferErrorMonad m where
  throwInferError :: InferError -> m a

runInfer' :: Collect a r => a
                        -> Context
                        -> Signature
                        -> (Either InferError (InferRes r), [Char])
runInfer' e ctx signature = evalState (runWriterT (runReaderT 
              (runExceptT (collectConstraints ctx e)) signature)) letters

runInfer :: (InferErrorMonad m, InferLogMonad m, Collect a r) 
         => a -> Context -> Signature -> m (InferRes r)
runInfer e ctx signature = do
  let (res, ilog) = runInfer' e ctx signature
  inferLog ilog
  case res of
    Left err -> throwInferError err
    Right res' -> return res'

runInferIO :: (Show r, Collect p r) => p -> Signature 
                                    -> IO (Either InferError (InferRes r))
runInferIO e signature = do
    let (res, info) = runInfer' e emptyCtx signature
    case res of
      Right r -> putStrLn $ "the inferred result is: " ++ show r
      Left err -> red $ "error in typechecking: " ++ show err
    putStrLn "-------------------"
    yellow $ "infer log: " ++ info
    return res

