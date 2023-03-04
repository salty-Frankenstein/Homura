{-# LANGUAGE OverloadedStrings #-}
module Lib.EDSL where
import Core
import Type 

v = Var
i = Lit . LInt
b = Lit . LBool 
unit = Lit LUnit
ret = Ret
a <| b = App a b 
l = id 
a .> b = Abs a b
o = OpTag
(<~) x y = (l "x" .> OpCall x  (v "x") "y" (Ret (v "y"))) <| y
c1 >-> _c2 = Let "_" c1 _c2

t = (l "x" .> Ret (v "x")) <| i 1
-- >>> t
-- (\x . return x) 1

-- >>> exec' t 
-- return 1
t1 = WithHandle (Handler "x" undefined (Ret (i 1)) 
                        ( OpCase (o "print") "x" "k" (Ret (v "x"))
                          (Nil undefined)))
c1 = Ret (b True)
c2 = o "print" <~ i 2
-- >>> exec' $ t1 c2
-- return 2
