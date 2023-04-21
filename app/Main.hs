module Main (main) where

import Interpreter

main :: IO ()
main = do
  -- let fileName = "./examples/poly.hmr"
  -- runInterpreter $ loadfile fileName
  runInterpreter runRepl
