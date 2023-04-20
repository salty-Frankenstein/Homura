{-# LANGUAGE OverloadedStrings #-}
module Type where

import Prelude hiding ((<>))
import qualified Data.Text as T
import qualified Data.Set.Monad as Set
import qualified Data.Map as Map
import Control.Monad.State
import Utils.Pretty
import Text.PrettyPrint
import Common

newtype TVar = TV Id
  deriving (Show, Eq, Ord)

newtype DVar = DV Id
  deriving (Show, Eq, Ord)

data PureType
  = TVar TVar
  | TCon Id -- TODO: top, bottom, int, bool
  | TFunc PureType DirtyType
  | THandler DirtyType DirtyType
  deriving (Eq, Ord)

typeInt = TCon "Int"
typeBool = TCon "Bool"
typeTop = TCon "Top"
typeBottom = TCon "Bottom"

data DirtyType
  = DirtyType PureType Dirt
  deriving (Eq, Ord)

-- TODO: check this definition later
data Dirt = Dirt (Set.Set OpTag) DVar
  deriving (Eq, Ord)

dirtVar :: Id -> Dirt
dirtVar d = Dirt Set.empty (DV d)

typeVar :: Id -> PureType
typeVar t = TVar (TV t)

class Rename a where
  -- apply a renaming mapping
  apply :: Map.Map Id Id -> a -> a

  free :: a -> VarSet

  normalize :: a -> a
  normalize a = let s = evalState (normalize' a) letters
                 in apply s a

  normalize' :: a -> State [Id] (Map.Map Id Id)
  normalize' a = do
    let fv = free a
    nn's <- forM (Set.toList fv) $ \n -> do
      n' <- getFreshName
      return (n, n')
    return (Map.fromList nn's)
    where
      getFreshName = do
        xs <- get
        put (tail xs)
        return (head xs)

instance Rename PureType where
  apply s t = case t of
    (TVar (TV a)) -> TVar . TV $ Map.findWithDefault a a s
    t@TCon{} -> t
    TFunc a d -> TFunc (apply s a) (apply s d)
    THandler d1 d2 -> THandler (apply s d1) (apply s d2)

  free TCon{} = Set.empty
  free (TVar (TV a)) = Set.singleton a
  free (TFunc a1 a2) = free a1 \/ free a2
  free (THandler d1 d2) = free d1 \/ free d2

instance Rename DirtyType where
  apply s (DirtyType a d) = DirtyType (apply s a) (apply s d)

  free (DirtyType a d) = free a \/ free d

instance Rename Dirt where
  apply s (Dirt ops (DV d)) = Dirt ops (DV (Map.findWithDefault d d s))

  free (Dirt _ (DV d)) = Set.singleton d

instance Pretty PureType where
  ppr _ (TVar (TV v)) = text v
  ppr _ (TCon c) = text c
  ppr p (TFunc t1 (DirtyType a d)) = parensIf p $ ppr 1 t1 
                                       <+> "-{" <> ppr 1 d <> "}->" <+> ppr 1 a
  ppr p (THandler t1 t2) = parensIf p $ ppr 1 t1 <+> "=>" <+> ppr 1 t2

instance Pretty DirtyType where
  ppr p (DirtyType t1 t2) = parensIf p $ ppr 1 t1 <> "!" <> ppr 1 t2

instance Pretty Dirt where
  ppr _ (Dirt t (DV d)) | Set.null t = text d
                        | otherwise = text (show (Set.toList t) ++ "|") <> text d

instance Show PureType where 
  show = render . pp 
instance Show DirtyType where 
  show = render . pp
instance Show Dirt where
  show = render . pp
