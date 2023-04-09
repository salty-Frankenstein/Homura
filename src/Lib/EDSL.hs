{-# LANGUAGE OverloadedStrings #-}
module Lib.EDSL where
import Common
import Syntax
import Type
import Data.String
import qualified Data.Text as T
import Control.Monad.Writer

{- overloading string literals for variables, operation tags and patterns -}
newtype Expr' = Expr' { unwrapE :: Expr}
instance IsString Expr' where
  fromString = Expr' . Var . T.pack

newtype OpTag' = OpTag' { unwrapOp :: OpTag }
instance IsString OpTag' where
  fromString = OpTag' . OpTag . T.pack

newtype Pattern' = Pattern' Pattern
instance IsString Pattern' where
  fromString = Pattern' . PVar . T.pack

-- literal expressions
i = Expr' . Lit . LInt
b = Expr' . Lit . LBool
true = b True
false = b False
unit = Expr' $ Lit LUnit

-- patterns
__ = Pattern' PWild
p0 x = Pattern' $ PCons x []
p1 x (Pattern' y1) = Pattern' $ PCons x [y1]
p2 x (Pattern' y1) (Pattern' y2) = Pattern' $ PCons x [y1, y2]
p3 x (Pattern' y1) (Pattern' y2) (Pattern' y3) = Pattern' $ PCons x [y1, y2, y3]

-- computations
ret = Ret . unwrapE
(Expr' a) <| (Expr' b) = App a b []
(Expr' a) .$ (Expr' b : bs) = App a b (unwrapE <$> bs)
_ .$ _ = undefined
if' (Expr' a) = If a 
c1 >-> _c2 = Do [Bind "_" c1] _c2 
(OpTag' x) </ (Expr' y) = OpCall x y
h |=> c = WithHandle h c 

(~>) :: Pattern' -> Computation -> Writer [(Pattern, Computation)] ()
(Pattern' p) ~> c = tell [(p, c)] 

match :: Expr' -> Writer [(Pattern, Computation)] a -> Computation
match (Expr' e) x = let res = execWriter x
                     in Case e res

(<~) :: Id -> Computation -> Writer [DoStmt] ()
x <~ c = tell [Bind x c]

do' :: Writer [DoStmt] () -> Computation -> Computation
do' x = let res = execWriter x
         in Do res 

let' x e c = Let x (unwrapE e) c

-- expressions
lam = id
a .> b = Expr' $ Abs a [] b

fun [] c = undefined 
fun [x] c = x .> c
fun (x:xs) c = Expr' $ Abs x xs c

opcase op = OpCase (unwrapOp op)
-- TODO: fix it later
handler x = Handler x undefined 
nil = Nil undefined
c0 x = Expr' $ Cons x []
c1 x (Expr' y1) = Expr' $ Cons x [y1]
c2 x (Expr' y1) (Expr' y2) = Expr' $ Cons x [y1, y2]
c3 x (Expr' y1) (Expr' y2) (Expr' y3) = Expr' $ Cons x [y1, y2, y3]
