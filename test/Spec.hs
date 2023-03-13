{-# LANGUAGE OverloadedStrings #-}
import qualified Syntax as S
import qualified Core as C
import Desugar

decls = [
    S.DataDecl "Expr" [
      S.TypeTerm "Var" ["Id"]
    , S.TypeTerm "Abs" ["Id", "Computation"]
    , S.TypeTerm "Handler" ["Id", "PureTerm", "Computation", "OpCase"]
    , S.TypeTerm "Arith" ["Arith"]
    , S.TypeTerm "ADT" ["ADT"]
    ]
  , S.DataDecl "Lit" [
      S.TypeTerm "LInt" ["Int"]
    , S.TypeTerm "LBool" ["Bool"]
    , S.TypeTerm "LUnit" []
    ]
  ]

a ~> b = (a, b)
i = S.Lit . S.LInt
c = S.Case (S.Lit (S.LInt 1)) [
    S.PCons "Add" [S.PCons "LInt" [S.PWild], S.PWild] ~> S.Ret (i 2)
  , S.PWild ~> S.Ret (i 3)
  ]

testcase :: S.Expr -> S.Computation
testcase e = S.Case e [
    S.PCons "Add" [S.PCons "Zero" [], S.PCons "Zero" []] ~> S.Ret (i 1)
  , S.PCons "Mul" [S.PCons "Zero" [], S.PVar "x"] ~> S.Ret (i 2)
  , S.PCons "Add" [S.PCons "Succ" [S.PVar "x"], S.PVar "y"] ~> S.Ret (i 3)
  , S.PCons "Mul" [S.PVar "x", S.PCons "Zero" []] ~> S.Ret (i 4)
  , S.PCons "Mul" [S.PCons "Add" [S.PVar "x", S.PVar "y"], S.PVar "z"] ~> S.Ret (i 5)
  , S.PCons "Add" [S.PVar "x", S.PCons "Zero" []] ~> S.Ret (i 6)
  , S.PVar "x" ~> S.Ret (i 7)
  ]

testCaseinput = [
    S.ADT (S.Cons "Add" [S.ADT (S.Cons "Zero" []), S.ADT (S.Cons "Zero" [])])
  , S.ADT (S.Cons "Add" [S.ADT (S.Cons "Succ" [i 1]), S.ADT (S.Cons "Zero" [])])
  , S.ADT (S.Cons "Add" [S.ADT (S.Cons "Zero" []), S.ADT (S.Cons "Succ" [i 1])])
  , S.ADT (S.Cons "Add" [S.ADT (S.Cons "Succ" [i 1]), S.ADT (S.Cons "Succ" [i 1])])
  , S.ADT (S.Cons "Mul" [S.ADT (S.Cons "Zero" []), S.ADT (S.Cons "Zero" [])])
  , S.ADT (S.Cons "Mul" [S.ADT (S.Cons "Succ" [i 1]), S.ADT (S.Cons "Zero" [])])
  , S.ADT (S.Cons "Mul" [S.ADT (S.Cons "Zero" []), S.ADT (S.Cons "Succ" [i 1])])
  , S.ADT (S.Cons "Mul" [S.ADT (S.Cons "Succ" [i 1]), S.ADT (S.Cons "Succ" [i 1])])
  ]

main :: IO ()
main = do
  putStrLn ""
  -- let (tm, t) = S.nameResolution decls
  -- putStrLn $ "tm: " ++ show tm
  -- putStrLn $ "t: " ++ show t
  -- print testcase
  let tests = desugar . testcase <$> testCaseinput
  -- print tests
  print (C.exec' <$> tests)
  return ()
