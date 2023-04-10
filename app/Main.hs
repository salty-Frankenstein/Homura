module Main (main) where

import Parser
import Infer.Infer
import Infer.Unify
import Syntax

main :: IO ()
main = do
  let fileName = "./examples/t.hmr"
  res <- parseHmr fileName
  case res of
    Left err -> print err
    Right (Program decls c) -> do
      let (tm, cs, os) = nameResolution decls
      putStr "tm: " >> print tm
      putStr "cs: " >> print cs
      putStr "os: " >> print os
      print c
