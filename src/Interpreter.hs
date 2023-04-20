{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
module Interpreter where

import Common
import Parser
import Type
import Infer.Infer
import Infer.Unify
import Syntax
import qualified Core as C
import Desugar
import Control.Monad.Reader
import Control.Monad.Except
import Data.IORef 
import qualified Data.Map as Map
import System.IO (hFlush, stdout)

data InterpState = InterpState 
                     { termMap :: IORef C.TermMap
                     , monoCtx :: IORef PolyCtx
                     , consSig :: IORef ConsSignature
                     , opSig   :: IORef OpSignature}

data InterpError = ParseError String
                 | TypeInferError InferError
                 | UnifyError String
                 | RuntimeError C.ExecError

instance Show InterpError where
  show (ParseError e) = e
  show (TypeInferError e) = show e
  show (UnifyError e) = e
  show (RuntimeError e) = show e

class ( 
      --   InferMonad m
      -- , UnifyMonad m
        MonadReader InterpState m
      , MonadError InterpError m
      , MonadIO m
      ) => InterpretMonad m where
  getContext :: m (C.TermMap, PolyCtx, ConsSignature, OpSignature)
  getContext = do
    InterpState tmR pctxR csR osR <- ask
    tm <- liftIO $ readIORef tmR
    pctx <- liftIO $ readIORef pctxR
    cs <- liftIO $ readIORef csR
    os <- liftIO $ readIORef osR
    return (tm, pctx, cs, os)

type InterpretM = (ReaderT InterpState (ExceptT InterpError IO))
instance InterpretMonad InterpretM 

runInterpreter :: InterpretM () -> IO ()
runInterpreter m = do
  tm <- newIORef Map.empty
  mctx <- newIORef Map.empty
  cs <- newIORef Map.empty
  os <- newIORef Map.empty
  res <- runExceptT (runReaderT m (InterpState tm mctx cs os))
  case res of
    Left err -> print err
    Right _ -> return ()

repl :: InterpretMonad m => m ()
repl = do
  liftIO $ putStr "homura> " >> hFlush stdout
  str <- liftIO getLine
  case str of
    [] -> repl
    ':':cmd -> doCmd cmd
    expr -> undefined
  where
    doCmd s 
      | c == "q" = liftIO $ putStrLn "See you next time (o>_<)o"
      | otherwise = do
          case c of
            "l" -> mapM_ loadfile xs
            "?" -> showHelp
            "context" -> showContext
            _ -> liftIO $ putStrLn $ "unknown command " ++ show c ++ 
                                      "\nuse :? for help."
          repl
      where (c:xs) = words s
    
    showHelp = do 
      liftIO $ putStrLn "help >_<"

    showContext :: InterpretMonad m => m ()
    showContext = do
      (tm, pctx, cs, os) <- getContext
      liftIO $ putStrLn "context: "
      liftIO $ print tm
      liftIO $ print pctx
      liftIO $ print cs
      liftIO $ print os


loadfile :: InterpretMonad m => FilePath -> m ()
loadfile fileName = do
  ---------- parsing ----------
  res <- liftIO $ parseHmr fileName
  case res of
    Left err -> throwError $ ParseError $ show err
    Right (Program decls c) -> do
      InterpState tmR pctxR csR osR <- ask
      let (tm', cs', os') = nameResolution decls
      liftIO $ modifyIORef' tmR (Map.union (Map.map desugar (Map.fromList tm')))
      liftIO $ modifyIORef' csR (Map.union cs')
      liftIO $ modifyIORef' osR (Map.union os')

      ------------- typechecking -------------
      forM_ tm' $ \(a, b) -> do
        liftIO $ putStrLn $ "now inferring: " ++ show a ++ ", " ++ show b
        liftIO $ hFlush stdout
        Res x y z <- typecheck b
        liftIO $ putStrLn $ "inferred type: " ++ show (Forall x y z)
        liftIO $ hFlush stdout
        liftIO $ modifyIORef' pctxR (Map.insert a (Forall x y z))

      (tm, pctx, cs, os) <- getContext
      liftIO $ putStrLn "the program is: "
      liftIO $ print c
      liftIO $ putStrLn "with context: "
      liftIO $ print tm'
      liftIO $ print pctx
      liftIO $ print cs
      liftIO $ print os

      case c of
        Just c -> do
          --- typechecking the main program ---
          _ <- typecheck c
          liftIO $ putStrLn "-------executing---------"
          x <- runComputation c -- TODO
          liftIO $ putStrLn "-------result---------"
          liftIO $ print x
        Nothing -> return ()

typecheck :: ( Show r, Substitutable r, Collect a r
             , InterpretMonad m
             ) => a -> m (InferRes r)
typecheck c = do
  (_, pctx, cs, os) <- getContext
  -- Res f a cstr <- collectConstraints (Context Map.empty pctx) c
  -- unify cstr
  -- (s, c) <- getUnifyRes

  -- undefined

  let (res, log) = runInfer c (Context Map.empty pctx) (Signature cs os)
  case res of
    Left err -> throwError $ TypeInferError err
    Right (Res f a cstr) -> do
      let (res, _) = runUnify cstr
      case res of
        Left err -> throwError $ UnifyError err
        Right (UnifyState s c _) -> do
          let t = normalize $ s ?$ a
          liftIO $ yellow log
          liftIO $ hFlush stdout
          liftIO $ red $ show a
          liftIO $ green $ show (s ?$ a)
          return (Res f t (toConsSet c))

runComputation :: InterpretMonad m => Computation -> m C.Result
runComputation c = do
  InterpState tmR _ _ _ <- ask
  tm <- liftIO $ readIORef tmR
  let c' = desugar c 
  res <- liftIO $ C.exec tm c'
  case res of
    Left err -> throwError $ RuntimeError err
    Right r -> return r
