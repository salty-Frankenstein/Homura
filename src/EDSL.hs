{-# LANGUAGE OverloadedStrings #-}
module EDSL where
import Core
import Type 

v = Var
i = Lit . LInt
b = Lit . LBool 
unit = Lit LUnit
a <| b = App a b 
l = id 
a .> b = Abs a b
o = OpTag
t = (l "x" .> Ret (v "x")) <| (i 1)
-- >>> t
-- (\x . return x) 1

-- >>> exec' t 
-- return 1
t1 = WithHandle (Handler "x" undefined (Ret (i 1)) 
                        ( OpCase (o "print") "x" "k" (Ret (v "x"))
                          (Nil undefined)))
c1 = Ret (b True)
c2 = OpCall (o "print") (i 2) "y" (Ret (v "y"))
-- >>> t1 c1
-- with (handler {return x -> return 1, print(x;k) -> return x ;}) handle (return True)
-- >>> exec' (t1 c1)
-- return 1
-- >>> exec' (t1 c2)
-- return 2
                
