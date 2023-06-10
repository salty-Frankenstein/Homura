{-# LANGUAGE OverloadedStrings #-}
module Lib.Arith where

import Syntax
import Lib.EDSL 

genBinOP' op = Abs "x" ["y"] (Arith $ BOp op (Var "x") (Var "y"))
genBinOP op = fun ["x", "y"] $ Arith $ BOp op (Var "x") (Var "y")
add = genBinOP Add
sub = genBinOP Sub
binop' f x y = App f x [y]
binop (Expr' f) (Expr' x) (Expr' y) = App f x [y]
(?+) = binop add
tx = i 6 ?+ i 8
ty = Do [Bind "x" (i 1 ?+ i 2)] ("x" ?+ i 3)
tz = (i 1 ?+ i 2) >-> ("_" ?+ i 3) >-> ("_" ?+ i 10)
-- >>> ty
-- let x <- let f <- (\x . return (\y . return (x + y))) 1 in (f 2) in (let f <- (\x . return (\y . return (x + y))) x in (f 3))
-- >>> exec' tz
-- return 16

-- max' = lam "x" .> ret (lam "y" .>  
--       If (Arith $ BOp Gt (Var "x") (Var "y"))
--         (ret "x")
--         (ret "y"))
