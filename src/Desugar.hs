{-# LANGUAGE OverloadedStrings #-}
module Desugar (desugar) where

import Common
import qualified Syntax as S 
import qualified Core as C 
import qualified Data.Text as T
import qualified Data.Set as Set
import Data.List (partition)
import Data.Maybe (catMaybes)

desugar :: S.Computation -> C.Computation
desugar sc = case sc of
  S.Ret e -> C.Ret (desugarExpr e)
  S.App e1 e2 -> C.App (desugarExpr e1) (desugarExpr e2)
  S.If e c1 c2 -> C.If (desugarExpr e) (desugar c1) (desugar c2)
  S.OpCall op e -> C.OpCall op (desugarExpr e) "y" (C.Ret (C.Var "y"))
  S.WithHandle e c -> C.WithHandle (desugarExpr e) (desugar c)
  S.Absurd d e -> C.Absurd d (desugarExpr e)
  S.Let x c1 c2 -> C.Let x (desugar c1) (desugar c2)
  S.LetRec f x c1 c2 -> C.LetRec f x (desugar c1) (desugar c2)
  cs@S.Case{} -> desugarCase cs

desugarExpr :: S.Expr -> C.Expr
desugarExpr se = case se of
  S.Var x -> C.Var x
  S.Lit v -> C.Lit (desugarLit v)
  S.Abs x c -> C.Abs x (desugar c)
  S.Handler x p c ocs -> C.Handler x p (desugar c) (desugarOp ocs)
  S.Arith a -> C.Arith (desugarArith a)
  S.ADT a -> C.ADT (desugarADT a)

desugarLit :: S.Lit -> C.Lit
desugarLit (S.LInt i) = C.LInt i
desugarLit (S.LBool b) = C.LBool b
desugarLit S.LUnit = C.LUnit

desugarOp :: S.OpCase -> C.OpCase
desugarOp (S.Nil x) = C.Nil x
desugarOp (S.OpCase op x k c ocs) = C.OpCase op x k (desugar c) (desugarOp ocs)

desugarADT :: S.ADT -> C.ADT
desugarADT (S.Inl e) = C.Inl (desugarExpr e)
desugarADT (S.Inr e) = C.Inr (desugarExpr e)
desugarADT (S.Prod e1 e2) = C.Prod (desugarExpr e1) (desugarExpr e2)
desugarADT (S.Cons c es) = C.Cons c (desugarExpr <$> es)
desugarADT (S.Fold e) = C.Fold (desugarExpr e)
desugarADT (S.Unfold e) = C.Unfold (desugarExpr e)

desugarArith :: S.Arith -> C.Arith
desugarArith (S.BOp b e1 e2) = C.BOp (toCore b) (desugarExpr e1) (desugarExpr e2)
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
desugarArith (S.UOp u e) = C.UOp (toCore u) (desugarExpr e)
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
                               in C.Let x (C.Ret (desugarExpr e)) cm
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
        S.PVar x -> GenMatchLn ps' (S.Let x (S.Ret (S.Var a)) e')
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