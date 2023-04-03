{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FunctionalDependencies #-}
module Desugar (desugar) where

import Common
import qualified Syntax as S 
import qualified Core as C 
import qualified Data.Text as T
import qualified Data.Set.Monad as Set
import Data.List (partition)
import Data.Maybe (catMaybes)

class Desugar a r | a -> r where
  desugar :: a -> r

instance Desugar S.Computation C.Computation where
  desugar sc = case sc of
    S.Ret e -> C.Ret (desugar e)
    S.App e1 e2 -> C.App (desugar e1) (desugar e2)
    S.If e c1 c2 -> C.If (desugar e) (desugar c1) (desugar c2)
    S.OpCall op e -> C.OpCall op (desugar e) "y" (C.Ret (C.Var "y"))
    S.WithHandle e c -> C.WithHandle (desugar e) (desugar c)
    S.Absurd d e -> C.Absurd d (desugar e)
    S.Let x e c -> C.Let x (desugar e) (desugar c)
    S.Do x c1 c2 -> C.Do x (desugar c1) (desugar c2)
    S.DoRec f x c1 c2 -> C.DoRec f x (desugar c1) (desugar c2)
    cs@S.Case{} -> desugarCase cs

instance Desugar S.Expr C.Expr where
  desugar se = case se of
    S.Var x -> C.Var x
    S.Lit v -> C.Lit (desugar v)
    S.Abs x c -> C.Abs x (desugar c)
    S.Handler x p c ocs -> C.Handler x p (desugar c) (desugar ocs)
    S.Arith a -> C.Arith (desugar a)
    S.ADT a -> C.ADT (desugar a)

instance Desugar S.Lit C.Lit where
  desugar (S.LInt i) = C.LInt i
  desugar (S.LBool b) = C.LBool b
  desugar S.LUnit = C.LUnit

instance Desugar S.OpCase C.OpCase where
  desugar (S.Nil x) = C.Nil x
  desugar (S.OpCase op x k c ocs) = C.OpCase op x k (desugar c) (desugar ocs)

instance Desugar S.ADT C.ADT where
  desugar (S.Inl e) = C.Inl (desugar e)
  desugar (S.Inr e) = C.Inr (desugar e)
  desugar (S.Prod e1 e2) = C.Prod (desugar e1) (desugar e2)
  desugar (S.Cons c es) = C.Cons c (desugar <$> es)
  desugar (S.Fold e) = C.Fold (desugar e)
  desugar (S.Unfold e) = C.Unfold (desugar e)

instance Desugar S.Arith C.Arith where
  desugar (S.BOp b e1 e2) = C.BOp (toCore b) (desugar e1) (desugar e2)
    where
      toCore b = case b of
        S.Add -> C.Add
        S.Sub -> C.Sub
        S.Mul -> C.Mul
        S.Div -> C.Div
        S.Eq -> C.Eq
        S.Lt -> C.Lt
        S.Gt -> C.Gt
        S.And -> C.And
        S.Or -> C.Or
  desugar (S.UOp u e) = C.UOp (toCore u) (desugar e)
    where
      toCore S.Neg = C.Neg
      toCore S.Not = C.Not

{-
- desugaring pattern matching
- the frontend language will be first transformed into an IR
- and then be desugared to the core
-}
-- the intermediate representation of pattern matching
-- with multiple patterns in a single line
newtype GenMatch = GenMatch [GenMatchLn] 
data GenMatchLn = GenMatchLn [(Id, S.Pattern)] S.Computation

desugarCase :: S.Computation -> C.Computation
desugarCase c@(S.Case e ps) = let x = freshName (S.freeVars c)
                                  cm = toCoreMatch $ toIR ps x
                               in C.Do x (C.Ret (desugar e)) cm
desugarCase _ = error "arg mismatch"

toIR :: [(S.Pattern, S.Computation)] -> Id -> GenMatch
toIR ls x = GenMatch $ (\(p, c) -> GenMatchLn [(x, p)] c) <$> ls

toCoreMatch :: GenMatch -> C.Computation
toCoreMatch x = let x' = step1 x
                 in case step2 x' of
                   Left c -> c
                   Right (a, S.PCons c ps) -> 
                     let fvs = freshNames (Set.unions $ S.freeVars <$> ps)
                         a1_n = take (length ps) fvs
                         (br_a, br_b) = step4 x' c a a1_n
                      in C.Case (C.Var a) c a1_n
                           (toCoreMatch br_a)
                           (toCoreMatch br_b)
                   _ -> error ""
                  
  where
    -- step1: push all bare variable patterns to the rhs using `let`
    step1 :: GenMatch -> GenMatch
    step1 (GenMatch ls) = GenMatch $ pushIn <$> ls
    pushIn :: GenMatchLn -> GenMatchLn
    pushIn (GenMatchLn [] e) = GenMatchLn [] e
    pushIn (GenMatchLn ((a, p):ps) e) = let GenMatchLn ps' e' = pushIn (GenMatchLn ps e)
      in case p of
        S.PWild -> undefined -- TODO
        S.PCons{} -> GenMatchLn ((a, p):ps') e'
        S.PVar x -> GenMatchLn ps' (S.Do x (S.Ret (S.Var a)) e')
    -- step2: select one of the tests in the first clause
    -- the choice is heuristic, here I just take the first instead
    step2 :: GenMatch -> Either C.Computation (Id, S.Pattern)
    step2 (GenMatch ((GenMatchLn (x:_) _):_)) = Right x
    step2 (GenMatch []) = error "Error: Non-exhaustive pattern match."
    step2 (GenMatch ((GenMatchLn [] c):_)) = Left (desugar c)
    -- step4: split the original patterns into two groups `A` and `B`
    step4 :: GenMatch 
          -> Id                   -- the constructor of the selected pattern
          -> Id                   -- the bound var to be matched
          -> [Id]                 -- the freevars generated 
          -> (GenMatch, GenMatch) -- the result, for `A` and `B` respectively
    step4 (GenMatch ls) c a vars = let (as, bs) = unzip $ split <$> ls 
                                    in (GenMatch (catMaybes as), GenMatch (catMaybes bs))
      where
        split :: GenMatchLn -> (Maybe GenMatchLn, Maybe GenMatchLn)
        split t@(GenMatchLn ps cm) = let (as, rest) = partition (\(x, _) -> x == a) ps
                                    in case as of
                                      (_, S.PCons c' ps'):xs -> if c' == c
                                        then (Just $ GenMatchLn (zip vars ps' ++ xs ++ rest) cm, Nothing)
                                        else (Nothing, Just t)
                                      [] -> (Just t, Just t)     -- contains no tests for a
                                      _ -> error "something wrong with the prior phase"

instance Show GenMatch where
  show (GenMatch ls) = "genmatch " ++ show ls
instance Show GenMatchLn where 
  show (GenMatchLn ps c) = foldr (\x y -> x++", "++y) "" 
                                 ((\(x, p) -> T.unpack x ++ " is " ++ show p) <$> ps)
                           ++ " => " ++ show c