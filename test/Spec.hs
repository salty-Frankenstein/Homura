{-# LANGUAGE OverloadedStrings #-}
import qualified Syntax as S
import qualified Core as C
import Common
import Desugar
import Lib.EDSL
import Lib.Arith
import Test.HUnit
import Infer.Infer
import Infer.Unify
import Type
import qualified Data.Map as Map

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
    do' "b" ("decide" <~ unit)
      (if' "b" (ret "x") (ret "y")))

chooseDiff = do' "x1" (binop choose (i 15) (i 30))
              (do' "x2" (binop choose (i 5) (i 10))
              (do' "diff" (binop sub "x1" "x2")
              (ret "diff")))
pickMax = handler "x" (ret "x")
                  (opcase "decide" "_" "k" 
                    (do' "xt" ("k" <| true)
                    (do' "xf" ("k" <| false)
                    (do' "max" (binop max' "xt" "xf")
                    (ret "max")))) 
                  nil)

pickTrue = handler "x" (ret "x")
                  (opcase "decide" "_" "k" 
                    ("k" <| true) 
                  nil)

run = C.exec' . desugar
cres = C.VRet . C.Lit . C.LInt

-- t :: InferM (InferRes PureType)
-- t = collectConstraints (Context Map.empty Map.empty) pickTrue

testInfer :: (Rename r, Substitutable r, Show r, Show a, Collect a r) 
          => a -> Signature -> IO ()
testInfer x s = do
  putStrLn "==========================="
  putStrLn $ "infering term: " ++ show x
  res <- runInferIO x s
  putStrLn "----------\nunification:"
  case res of
    Right (Res _ a c) -> case runUnify c of
      Left s -> do 
        red $ "error in unification: "
        red s
      Right (UnifyState s c _) -> do
        putStrLn $ "the result substitution is: " ++ show s
        putStrLn $ "the result constraint set is: " ++ show c
        putStrLn $ "======================="
        let t = normalize $ s ?$ a
        green $ "result: " ++ show x ++ " : " ++ show t ++ "\ESC[0m"
    _ -> return ()

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

  let decideSig = Map.fromList [(OpTag "decide", (typeTop, typeBool))]
  testInfer pickTrue decideSig
  testInfer (unwrapE $ fun "f" .> ret (fun "x" .> ("f" <| "x"))) Map.empty
  let poly1 = let' "f" (fun "x" .> ret "x") 
                (do' "b" ("f" <| true)
                  (if' "b" ("f" <| i 1) ("f" <| i 2)))
  let poly2 = let' "const" (fun "y" .> ret (fun "x" .> ret "y")) 
                (let' "c1" (fun "x" .> do' "f" ("const" <| i 1) ("f" <| "x"))
                  (if' true ("c1" <| true) ("c1" <| i 1)))
  testInfer poly1 Map.empty
  testInfer poly2 Map.empty
  -- testInfer chooseDiff decideSig

  return ()
