{-# LANGUAGE OverloadedStrings #-}
module Common where

import qualified Data.Set.Monad as Set
import qualified Data.Map as Map
import Data.String
import Control.Monad

type Id = String
type VarSet = Set.Set Id

newtype OpTag = OpTag Id deriving (Eq, Ord)
newtype ConsName = ConsName Id deriving (Eq, Ord)

instance Show ConsName where
  show (ConsName x) = x

instance IsString ConsName where
  fromString = ConsName

instance Show OpTag where
  show (OpTag t) = t

infixr 5 \/
(\/), (\\), (/\) :: Ord a => Set.Set a -> Set.Set a -> Set.Set a
(\/) = Set.union
(\\) = (Set.\\)
(/\) = Set.intersection

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
letters = [1..] >>= flip replicateM ['a'..'z']

color d s = putStrLn $ d ++ s ++ "\ESC[0m"
red = color "\ESC[31m"
yellow = color "\ESC[33m"
green = color "\ESC[32m"