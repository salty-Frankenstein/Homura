module Type where

import qualified Data.Text as T
import qualified Data.Set as Set

newtype OpTag = OpTag T.Text deriving (Show, Eq)

newtype TVar = TV T.Text
  deriving Show

data PureType
  = TVar TVar
  | TCon String -- TODO: top, bottom, int, bool
  | TFunc PureType DirtyType
  | THandler DirtyType DirtyType
  deriving Show

data DirtyType
  = DirtyType PureType Dirt
  deriving Show

newtype Dirt = Dirt (Set.Set T.Text)
  deriving Show