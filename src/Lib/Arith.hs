{-# LANGUAGE OverloadedStrings #-}
module Lib.Arith where

import Core
import Lib.EDSL 

add = l "x" .> ret (l "y" .> ret (Arith $ BOp Add (v "x") (v "y")))
sub = l "x" .> ret (l "y" .> ret (Arith $ BOp Sub (v "x") (v "y")))
binop f x y = Let "f" (f <| x) (v "f" <| y)
(?+) = binop add
tx = i 6 ?+ i 8
ty = Let "x" (i 1 ?+ i 2) (v "x" ?+ i 3)
tz = (i 1 ?+ i 2) >-> (v "_" ?+ i 3) >-> (v "_" ?+ i 10)
-- >>> ty
-- let x <- let f <- (\x . return (\y . return (x + y))) 1 in (f 2) in (let f <- (\x . return (\y . return (x + y))) x in (f 3))
-- >>> exec' tz
-- return 16

max' = l "x" .> ret (l "y" .>  
      If (Arith $ BOp Gt (v "x") (v "y"))
        (ret (v "x"))
        (ret (v "y")))

choose = l "x" .> ret (l "y" .>
    Let "b" (o"decide" <~ unit)
    (If (v "b")
      (ret (v "x"))
      (ret (v "y"))))

chooseDiff = Let "x1" (binop choose (i 15) (i 30))
              (Let "x2" (binop choose (i 5) (i 10))
              (Let "diff" (binop sub (v "x1") (v "x2"))
              (ret (v "diff"))))
pickMax = Handler "x" undefined (ret (v "x")) 
                  (OpCase (o"decide") "_" "k" 
                    (Let "xt" (v "k" <| b True)
                    (Let "xf" (v "k" <| b False)
                    (Let "max" (binop max' (v "xt") (v "xf"))
                    (ret (v "max"))))) 
                  (Nil undefined))

pickTrue = Handler "x" undefined (ret (v "x"))
                  (OpCase (o"decide") "_" "k" 
                    (v "k" <| b True) 
                  (Nil undefined))
{- >>> exec' (WithHandle pickTrue chooseDiff)
return 10
>>> exec' (WithHandle pickMax chooseDiff)
return 25
-}
