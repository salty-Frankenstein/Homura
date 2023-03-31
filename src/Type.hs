{-# LANGUAGE OverloadedStrings #-}
module Type where

import Prelude hiding ((<>))
import qualified Data.Text as T
import qualified Data.Set as Set
import Utils.Pretty
import Text.PrettyPrint
import Common

newtype OpTag = OpTag T.Text deriving (Show, Eq, Ord)

newtype TVar = TV T.Text
  deriving (Show, Eq, Ord)

newtype DVar = DV T.Text
  deriving (Show, Eq, Ord)

data PureType
  = TVar TVar
  | TCon Id -- TODO: top, bottom, int, bool
  | TFunc PureType DirtyType
  | THandler DirtyType DirtyType
  | TSum PureType PureType
  | TProd PureType PureType 
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
  deriving (Show, Eq, Ord)

instance Pretty PureType where
  ppr _ (TVar (TV v)) = "TVar" <+> text' v
  ppr _ (TCon c) = "TCon" <+> text' c
  ppr p (TFunc t1 t2) = parensIf p $ ppr 1 t1 <+> "->" <+> ppr 1 t2
  ppr p (THandler t1 t2) = parensIf p $ ppr 1 t1 <+> "=>" <+> ppr 1 t2
  ppr p (TSum t1 t2) = parensIf p $ ppr 1 t1 <+> "+" <+> ppr 1 t2
  ppr p (TProd t1 t2) = parensIf p $ ppr 1 t1 <+> "*" <+> ppr 1 t2

instance Pretty DirtyType where
  ppr p (DirtyType t1 t2) = parensIf p $ ppr 1 t1 <+> "!" <+> ppr 1 t2

instance Pretty Dirt where
  ppr _ (Dirt t d) = text $ show t ++ " | " ++ show d

instance Show PureType where 
  show = render . pp 
instance Show DirtyType where 
  show = render . pp
