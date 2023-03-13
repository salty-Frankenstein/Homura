{-# LANGUAGE OverloadedStrings #-}
import qualified Syntax as S
import qualified Core as C
import Desugar
import Lib.EDSL
import Lib.Arith
import Test.HUnit

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

c = match (i 1) $ do
      p2 "Add" (p1 "LInt" __) __ ~> ret (i 2)
      __ ~> ret (i 3)
  
testCase e = match e $ do 
               p2 "Add" (p0 "Zero") (p0 "Zero") ~> ret (i 1)
               p2 "Mul" (p0 "Zero") "x" ~> ret (i 2)
               p2 "Add" (p1 "Succ" "x") "y" ~> ret (i 3)
               p2 "Mul" "x" (p0 "Zero") ~> ret (i 4)
               p2 "Mul" (p2 "Add" "x" "y") "z" ~> ret (i 5)
               p2 "Add" "x" (p0 "Zero") ~> ret (i 6)
               "x" ~> ret (i 7)

testCaseinput = [
    c2 "Add" (c0 "Zero") (c0 "Zero")
  , c2 "Add" (c1 "Succ" (i 1)) (c0 "Zero")
  , c2 "Add" (c0 "zero") (c1 "Succ" (i 1)) 
  , c2 "Add" (c1 "Succ" (i 1)) (c1 "Succ" (i 1))  
  , c2 "Mul" (c0 "Zero") (c0 "Zero")
  , c2 "Mul" (c1 "Succ" (i 1)) (c0 "Zero")
  , c2 "Mul" (c0 "Zero") (c1 "Succ" (i 1)) 
  , c2 "Mul" (c1 "Succ" (i 1)) (c1 "Succ" (i 1))  
  , c2 "Mul" (c2 "Add" (i 1) (i 1)) (c1 "Succ" (i 1))  
  , c2 "Add" (c2 "Add" (i 1) (i 1)) (c0 "Zero")
  ]

choose = fun "x" .> ret (fun "y" .>
    let' "b" ("decide" <~ unit)
      (if' "b" (ret "x") (ret "y")))

chooseDiff = let' "x1" (binop choose (i 15) (i 30))
              (let' "x2" (binop choose (i 5) (i 10))
              (let' "diff" (binop sub "x1" "x2")
              (ret "diff")))
pickMax = handler "x" (ret "x")
                  (opcase "decide" "_" "k" 
                    (let' "xt" ("k" <| true)
                    (let' "xf" ("k" <| false)
                    (let' "max" (binop max' "xt" "xf")
                    (ret "max")))) 
                  nil)

pickTrue = handler "x" (ret "x")
                  (opcase "decide" "_" "k" 
                    ("k" <| true) 
                  nil)

run = C.exec' . desugar
cres = C.VRet . C.Lit . C.LInt

main :: IO ()
main = do
  putStrLn ""
  -- tests for `case`
  let tests = testCase <$> testCaseinput
      res = run <$> tests
      expected = cres <$> [1, 3, 7, 3, 2, 4, 2, 7, 5, 6]
      test1 = TestCase . uncurry (assertEqual "test1") <$> zip res expected

  -- tests for handlers
      res1 = run (pickTrue |=> chooseDiff)
      res2 = run (pickMax |=> chooseDiff)
      test2 = TestCase (assertEqual "test2" res1 (cres 10))
      test3 = TestCase (assertEqual "test3" res2 (cres 25))
  _ <- runTestTT (TestList $ test1 ++ [test2, test3])
  
  return ()
