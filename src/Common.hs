module Common where

import qualified Data.Text as T
import qualified Data.Set.Monad as Set
import qualified Data.Map as Map
import Control.Monad

type Id = T.Text
type VarSet = Set.Set Id

infixr 5 \/
(\/), (\\) :: Ord a => Set.Set a -> Set.Set a -> Set.Set a
(\/) = Set.union
(\\) = (Set.\\)

(?:) :: Ord k => Map.Map k a -> (k, a) -> Map.Map k a
m ?: (a, b) = Map.insert a b m

infixr 5 ?::
(?::) :: Ord a => a -> Set.Set a -> Set.Set a
(?::) = Set.insert

freshNames :: VarSet -> [Id]
freshNames s = filter (`Set.notMember` s) letters
freshName :: VarSet -> Id
freshName = head . freshNames
letters :: [Id]
letters = map T.pack $ [1..] >>= flip replicateM ['a'..'z']
