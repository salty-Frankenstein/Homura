module Interpreter where

import Common
import Parser
import Infer.Infer
import Infer.Unify
import Syntax
import qualified Core as C
import Desugar
import Control.Monad.Reader
import Data.IORef 
import qualified Data.Map as Map

data InterpState = InterpState 
                     { termMap :: IORef C.TermMap
                     , monoCtx :: IORef MonoCtx
                     , consSig :: IORef ConsSignature
                     , opSig   :: IORef OpSignature}

type InterpretM = ReaderT InterpState IO

runInterpreter :: InterpretM () -> IO ()
runInterpreter m = do
  tm <- newIORef Map.empty
  mctx <- newIORef Map.empty
  cs <- newIORef Map.empty
  os <- newIORef Map.empty
  runReaderT m (InterpState tm mctx cs os)

interpret :: IO ()
interpret = do
  return ()

loadfile :: FilePath -> InterpretM ()
loadfile fileName = do
  res <- liftIO $ parseHmr fileName
  case res of
    Left err -> liftIO $ print err
    Right (Program decls c) -> do
      InterpState tmR mctxR csR osR <- ask
      let (tm', cs', os') = nameResolution decls
      liftIO $ modifyIORef' tmR (Map.union (Map.map desugar tm'))
      liftIO $ modifyIORef' csR (Map.union cs')
      liftIO $ modifyIORef' osR (Map.union os')

      -------------------------------
      (tm, mctx, cs, os) <- getContext
      liftIO $ putStrLn "the program is: "
      liftIO $ print c
      liftIO $ putStrLn "with context: "
      liftIO $ print tm
      liftIO $ print mctx
      liftIO $ print cs
      liftIO $ print os

      liftIO $ putStrLn "-------result---------"
      x <- runComputation c -- TODO
      liftIO $ print x
      return ()

typeChecking :: Collect a r => a -> InterpretM (Maybe (InferRes r))
typeChecking c = do
  (_, mctx, cs, os) <- getContext
  let (res, _) = runInfer c (Context mctx Map.empty) (Signature cs os)
  case res of
    Left err -> liftIO . red $ "error in typechecking: " ++ showError err
    Right (Res _ a c) -> do
      let (res, _) = runUnify c
      case res of
        Left err -> liftIO . red $ "error in unification: " ++ err
        Right (UnifyState s c _) -> return ()
  -- TODO:
  return Nothing

runComputation :: Computation -> InterpretM (Either C.ExecError C.Result)
runComputation c = do
  InterpState tmR _ _ _ <- ask
  tm <- liftIO $ readIORef tmR
  let c' = desugar c 
  return $ C.exec tm c'

getContext :: InterpretM (C.TermMap, MonoCtx, ConsSignature, OpSignature)
getContext = do
  InterpState tmR mctxR csR osR <- ask
  tm <- liftIO $ readIORef tmR
  mctx <- liftIO $ readIORef mctxR
  cs <- liftIO $ readIORef csR
  os <- liftIO $ readIORef osR
  return (tm, mctx, cs, os)