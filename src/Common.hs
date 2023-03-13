module Common where

import qualified Data.Text as T
import qualified Data.Set as Set
import Control.Monad

type Id = T.Text
type VarSet = Set.Set Id
(\/), (\\) :: VarSet -> VarSet -> VarSet
(\/) = Set.union
(\\) = (Set.\\)

freshNames :: VarSet -> [Id]
freshNames s = filter (`Set.notMember` s) letters
freshName :: VarSet -> Id
freshName = head . freshNames
letters :: [Id]
letters = map T.pack $ [1..] >>= flip replicateM ['a'..'z']
