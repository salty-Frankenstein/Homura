{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
module Infer.Unify where

import qualified Data.Set.Monad as Set
import qualified Data.Map as Map
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Except
import Common
import Type
import Infer.Infer

data Substitution = Substitution
                      { pureMap :: Map.Map Id PureType
                      , dirtMap :: Map.Map Id Dirt } deriving Show

fromPureMap :: [(Id, PureType)] -> Substitution
fromPureMap x = Substitution (Map.fromList x) Map.empty
fromDirtMap :: [(Id, Dirt)] -> Substitution
fromDirtMap x = Substitution Map.empty (Map.fromList x)

compose :: Substitution -> Substitution -> Substitution
compose s1@(Substitution ps1 ds1) (Substitution ps2 ds2) =
  Substitution
    { pureMap = Map.map (s1 ?$) ps2 `Map.union` ps1
    , dirtMap = Map.map (s1 ?$) ds2 `Map.union` ds1 }

class Rename a => Substitutable a where
  (?$) :: Substitution -> a -> a

instance Substitutable PureType where
  subst@(Substitution s _) ?$ t = case t of
    t@(TVar (TV a)) -> Map.findWithDefault t a s
    t@TCon{} -> t
    TFunc a d -> TFunc (subst ?$ a) (subst ?$ d)
    THandler d1 d2 -> THandler (subst ?$ d1) (subst ?$ d2)

instance Substitutable DirtyType where
  subst ?$ DirtyType a d = DirtyType (subst ?$ a) (subst ?$ d)

instance Substitutable Dirt where
  Substitution _ s ?$ Dirt ops (DV d) = Dirt (ops \/ ops') d'
    where Dirt ops' d' = Map.findWithDefault (dirtVar d) d s

data UnifiedCons = UnifiedCons Id Id deriving (Eq, Ord)
data UnifiedConsSet = UnifiedConsSet
                        { pureCons :: Set.Set UnifiedCons
                        , dirtCons :: Set.Set UnifiedCons } deriving Show

emptyUniConsSet :: UnifiedConsSet
emptyUniConsSet = UnifiedConsSet Set.empty Set.empty 
fromPureSet, fromDirtSet :: Set.Set UnifiedCons -> UnifiedConsSet
fromPureSet s = UnifiedConsSet s Set.empty
fromDirtSet = UnifiedConsSet Set.empty

instance Show UnifiedCons where
  show (UnifiedCons a b) = a ++ " <= " ++ b

(?\) :: UnifiedConsSet -> UnifiedConsSet -> UnifiedConsSet
(UnifiedConsSet x1 x2) ?\ (UnifiedConsSet y1 y2) = UnifiedConsSet (x1 \\ y1) (x2 \\ y2)

toConsSet :: UnifiedConsSet -> ConsSet
toConsSet (UnifiedConsSet p d) = 
     Set.map (\(UnifiedCons a b) -> CPureTLE (typeVar a) (typeVar b)) p
  \/ Set.map (\(UnifiedCons a b) -> CDirtLE (dirtVar a) (dirtVar b)) d

instance Substitutable Constraint where
  subst ?$ CPureTLE a b = CPureTLE (subst ?$ a) (subst ?$ b)
  subst ?$ CDirtyTLE d1 d2 = CDirtyTLE (subst ?$ d1) (subst ?$ d2)
  subst ?$ CDirtLE d1 d2 = CDirtLE (subst ?$ d1) (subst ?$ d2)

instance Substitutable ConsSet where
  subst ?$ cs = (subst ?$) <$> cs

-- TODO: check if it keeps reflexive 
-- the closure operator for pure types
-- TODO: rewrite this
(\+/) :: UnifiedConsSet -> UnifiedCons -> UnifiedConsSet
(UnifiedConsSet _p d) \+/ UnifiedCons a1 a2 = UnifiedConsSet p' d
  where
    p = _p \/ Set.fromList [UnifiedCons a1 a1, UnifiedCons a2 a2]
    p' = p \/ [UnifiedCons a1' a2' | 
                UnifiedCons a1' y <- p, y == a1,
                UnifiedCons x a2' <- p, x == a2]
(\*/) :: UnifiedConsSet -> UnifiedCons -> UnifiedConsSet
(UnifiedConsSet p _d) \*/ UnifiedCons a1 a2 = UnifiedConsSet p d'
  where
    d = _d \/ Set.fromList [UnifiedCons a1 a1, UnifiedCons a2 a2]
    d' = d \/ [UnifiedCons a1' a2' | 
                UnifiedCons a1' y <- d, y == a1,
                UnifiedCons x a2' <- d, x == a2]

-- the equivalence class of same shape
equiv :: Set.Set UnifiedCons -> Id -> VarSet
equiv c a = a ?:: [y | UnifiedCons x y <- c, x == a]
         \/ [x | UnifiedCons x y <- c, y == a]

data UnifyState = UnifyState
                    { subst   :: Substitution   -- the collected subtitution & 
                    , consSet :: UnifiedConsSet -- the constraints already unified
                    , names   :: [Id] }         -- stream of fresh streams

class ( MonadState UnifyState m
      , MonadWriter String m
      , MonadError String m
      ) => UnifyMonad m where
  getUnifyRes :: m (Substitution, UnifiedConsSet)
  getUnifyRes = do
    s <- get
    return (subst s, consSet s)

  -- compose the current substitution with a given one
  composeWith :: Substitution -> m ()
  composeWith s' = modify (\(UnifyState s c n) -> UnifyState (compose s' s) c n)

  modifyConsSet :: (UnifiedConsSet -> UnifiedConsSet) -> m ()
  modifyConsSet f = modify (\(UnifyState s c n) -> UnifyState s (f c) n)

  getFreshName :: m Id
  getFreshName = do
    UnifyState s c xs <- get
    put (UnifyState s c (tail xs))
    return (head xs)

  -- returns a type of the same form
  -- except with all its type & dirt parameters replaced with fresh ones
  -- HACK: fresh names generated in this phase differs from the previous phase
  -- which prevents checking the freshness
  refresh :: PureType -> m PureType
  refresh t = case t of
      TVar _ -> TVar . TV <$> getFreshName
      x@TCon{} -> return x
      TFunc a d -> TFunc <$> refresh a <*> refreshDT d
      THandler d1 d2 -> THandler <$> refreshDT d1 <*> refreshDT d2
    where
      refreshDT (DirtyType a d) = DirtyType <$> refresh a <*> refreshD d
      refreshD (Dirt op _) = Dirt op . DV <$> getFreshName

-- TODO: 
pop :: Ord a => Set.Set a -> (a, Set.Set a)
pop s | Set.null s = undefined
      | otherwise = (Set.findMax s, Set.deleteMax s)

-- the unification algorithm
unify :: UnifyMonad m => ConsSet -> m ()
unify q' 
  | Set.null q' = return ()
  | otherwise = let (h, q) = pop q' in case h of
    CPureTLE a a' -> if a == a' then unify q
      else case (a, a') of
        -- a <= a'
        (TVar (TV a), TVar (TV a')) -> do
          modifyConsSet (\+/ UnifiedCons a a')
          unify q
        -- a <= A
        (_a@(TVar (TV a)), _A) -> do
          c <- gets $ pureCons . consSet
          let a's = equiv c a
          if any (`Set.member` free _A) a's
          then throwError $ "cannot unify: infinite type"
          else do
            ls' <- forM (Set.toList a's) $ \a' -> (,) a' <$> refresh _A
            let s' = fromPureMap ls'
                c' = fromPureSet [p | p@(UnifiedCons a' a'') <- c, a' `elem` a's, a'' `elem` a's]
            composeWith s'
            modifyConsSet (?\ c')
            -- TODO: check this
            -- let tt = (CPureTLE (s' ?$ _a) _A ?:: s' ?$ toConsSet c' \/ s' ?$ q)
            -- throwError $ show tt
            unify (CPureTLE (s' ?$ _a) _A ?:: s' ?$ toConsSet c' \/ s' ?$ q)
        -- A <= a
        (_A, _a@(TVar (TV a))) -> do
          c <- gets $ pureCons . consSet
          let a's = equiv c a
          if any (`Set.member` free _A) a's
          then throwError $ "cannot unify: infinite type"
          else do
            ls' <- forM (Set.toList a's) $ \a' -> (,) a' <$> refresh _A
            let s' = fromPureMap ls'
                c' = fromPureSet [p | p@(UnifiedCons a' a'') <- c, a' `elem` a's, a'' `elem` a's]
            composeWith s'
            modifyConsSet (?\ c')
            -- TODO: check this
            unify (CPureTLE _A (s' ?$ _a) ?:: s' ?$ toConsSet c' \/ s' ?$ q)
        (TFunc _A _C, TFunc _A' _C') -> unify (CPureTLE _A' _A ?:: CDirtyTLE _C _C' ?:: q)
        (THandler _C _D, THandler _C' _D') -> unify (CDirtyTLE _C' _C ?:: CDirtyTLE _D _D' ?:: q)
        -- TODO: more
        _ -> throwError $ "cannot unify " ++ show a ++ " and " ++ show a'
    CDirtyTLE (DirtyType a d) (DirtyType a' d') -> unify (CPureTLE a a' ?:: CDirtLE d d' ?:: q)
    CDirtLE (Dirt o (DV d1)) (Dirt o' (DV d2)) ->
      if o == o' then modifyConsSet (\*/ UnifiedCons d1 d2) >> unify q
      else do
        -- tell $ "\nunifying: " ++ show h ++ "\n"
        c <- gets $ dirtCons . consSet
        d1' <- getFreshName
        d2' <- getFreshName
        let s1 = fromDirtMap [(d1, Dirt (o' \\ o) (DV d1')) | not (o' `Set.isSubsetOf` o)]
            s2 = fromDirtMap [(d2, Dirt (o \\ o') (DV d2')) | not (o `Set.isSubsetOf` o')]
            s' = compose s1 s2
            d1's = equiv c d1
            d2's = equiv c d2
            c' = fromDirtSet $ [p | p@(UnifiedCons d d') <- c, d `elem` d1's, d' `elem` d1's]
                            \/ [p | p@(UnifiedCons d d') <- c, d `elem` d2's, d' `elem` d2's]
        -- tell $ show s1 ++ "\n"
        -- tell $ show s2 ++ "\n"
        composeWith s'
        modifyConsSet (?\ c')
        unify (s' ?$ toConsSet c' \/ s' ?$ q)

-- instantiate
type UnifyM = StateT UnifyState (ExceptT String (Writer String))
instance UnifyMonad UnifyM

class Monad m => UnifyErrorMonad m where
  throwUnifyError :: String -> m a

class Monad m => UnifyLogMonad m where
  unifyLog :: String -> m ()

runUnify' :: Set.Set Constraint -> (Either String UnifyState, String)
runUnify' q = runWriter $ runExceptT $ execStateT (unify q)
               (UnifyState (fromPureMap []) emptyUniConsSet (map ('_':) letters))

runUnify :: (UnifyErrorMonad m, UnifyLogMonad m) 
         => Set.Set Constraint -> m (Substitution, UnifiedConsSet)
runUnify q = do
  let (res, ulog) = runUnify' q
  unifyLog ulog
  case res of
    Left err -> throwUnifyError err
    Right (UnifyState s c _) -> return (s, c)
  
---- garbage collecting --
class Garbage a where
  pos :: a -> VarSet
  neg :: a -> VarSet

instance Garbage PureType where
  pos (TVar (TV a)) = Set.singleton a
  pos TCon{} = Set.empty
  pos (TFunc a c) = neg a \/ pos c
  pos (THandler c d) = neg c \/ pos d

  neg TVar{} = Set.empty
  neg TCon{} = Set.empty
  neg (TFunc a c) = pos a \/ neg c
  neg (THandler c d) = pos c \/ neg d

instance Garbage DirtyType where
  pos (DirtyType a (Dirt _ (DV d))) = pos a \/ Set.singleton d
  neg (DirtyType a _) = neg a

-- given a unified constraint set & set of parameters p and n
gc :: Garbage a => UnifiedConsSet -> a -> UnifiedConsSet
gc (UnifiedConsSet pc dc) a = UnifiedConsSet ps ds
  where
    p = pos a
    n = neg a
    ps = [ c | c@(UnifiedCons an ap) <- pc, Set.member an n, Set.member ap p]
    ds = [ c | c@(UnifiedCons dn dp) <- dc, Set.member dn n, Set.member dp p]

-- displaying simplificatoin
-- suppose the consset is already garbage collected
simplifyDirtVar :: UnifiedConsSet -> UnifiedConsSet
simplifyDirtVar = undefined


class Simplify a where
  simplify :: a -> a

instance Simplify Scheme where
  simplify (Forall f t c) = undefined
    
