module Main (main) where

import Interpreter

main :: IO ()
main = do
  let fileName = "./examples/pattern.hmr"
  runInterpreter $ loadfile fileName
  -- res <- parseHmr fileName
  -- case res of
  --   Left err -> print err
  --   Right (Program decls c) -> do
  --     let (tm, cs, os) = nameResolution decls
  --     putStr "tm: " >> print tm
  --     putStr "cs: " >> print cs
  --     putStr "os: " >> print os
  --     print c
