{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
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
import Control.Monad.Catch
import Data.IORef
import qualified Data.Map as Map
import System.IO (hFlush, stdout)
import System.Console.Haskeline
import System.Process
import Text.PrettyPrint

data InterpState = InterpState
                     { termMap :: IORef C.TermMap
                     , polyCtx :: IORef PolyCtx
                     , consSig :: IORef ConsSignature
                     , opSig   :: IORef OpSignature }

data InterpError = ParseError String
                 | TypeInferError InferError
                 | UnifyError String
                 | RuntimeError C.ExecError
instance Exception InterpError

instance Show InterpError where
  show (ParseError e) = e
  show (TypeInferError e) = show e
  show (UnifyError e) = e
  show (RuntimeError e) = show e

class ( MonadReader InterpState m
      , MonadIO m, MonadMask m
      ) => InterpretMonad' m where
  getContext :: m (C.TermMap, PolyCtx, ConsSignature, OpSignature)
  getContext = do
    InterpState tmR pctxR csR osR <- ask
    tm <- liftIO $ readIORef tmR
    pctx <- liftIO $ readIORef pctxR
    cs <- liftIO $ readIORef csR
    os <- liftIO $ readIORef osR
    return (tm, pctx, cs, os)

  interpLog :: String -> m ()

class ( InterpretMonad' m
      , InferErrorMonad m, InferLogMonad m
      , UnifyErrorMonad m, UnifyLogMonad m
      , ParseErrorMonad m
      , C.RuntimeErrorMonad m
      ) => InterpretMonad m

type InterpretM = (ReaderT InterpState (ExceptT InterpError IO))
instance InferErrorMonad InterpretM where
  throwInferError e = throwM (TypeInferError e)
instance InferLogMonad InterpretM where
  inferLog _ = return ()
  -- inferLog s = liftIO $ yellow s >> hFlush stdout
instance UnifyErrorMonad InterpretM where
  throwUnifyError e = throwM (UnifyError e)
instance UnifyLogMonad InterpretM where
  unifyLog _ = return ()
  -- unifyLog s = liftIO $ yellow s >> hFlush stdout
instance ParseErrorMonad InterpretM where
  throwParseError e = throwM (ParseError (show e))
instance C.RuntimeErrorMonad InterpretM where
  throwRuntimeError e = throwM (RuntimeError e)
instance InterpretMonad' InterpretM where
  interpLog _ = return ()
  -- interpLog s = liftIO $ putStrLn s >> hFlush stdout

instance InterpretMonad InterpretM

runInterpreter :: InterpretM () -> IO ()
runInterpreter m = do
  tm <- newIORef Map.empty
  mctx <- newIORef Map.empty
  cs <- newIORef Map.empty
  os <- newIORef definedOp
  res <- runExceptT (runReaderT m (InterpState tm mctx cs os))
  case res of
    Left err -> print err
    Right _ -> return ()
  where
    definedOp = Map.fromList [(OpTag "print", (typeInt, typeTop))
                             ,(OpTag "readInt", (typeTop, typeInt))]

runRepl :: InterpretM ()
runRepl = do
  liftIO $ putStrLn "Homura, version 0.1, :? for help"
  runInputT defaultSettings repl

repl :: InterpretMonad m => InputT m ()
repl = do
  str <- getInputLine "homura> "
  case str of
    Nothing -> return ()
    Just (':':cmd) -> doCmd cmd
    Just code -> catch (doCode code) errorHandler >> repl
  where
    doCode code = lift $ catch doWhite $ \case
                    ParseError _ -> catch doExpr $ \case
                      ParseError _ -> doComp
                      e -> throwM e
                    e -> throwM e
      where
        doWhite = do
          runParseWhite code

        doExpr = do
          e <- runParseExpr code
          _ <- typecheckExpr e
          res <- runExpr e
          liftIO $ print res

        doComp = do
          cm <- runParseComputation code
          _ <- typecheck cm
          res <- runComputation cm
          liftIO $ print res

    doCmd s = case words s of
      [] -> repl
      c:xs -> 
        if c == "q" then liftIO $ putStrLn "See you next time (o>_<)o"
        else do
          case c of
            "l" -> catch (lift (mapM_ loadfile xs)) errorHandler
            "t" -> catch (doType xs) errorHandler
            "?" -> showHelp
            "!" -> liftIO . void $ system (unwords xs)
            "context" -> lift showContext
            _ -> liftIO $ putStrLn $ "unknown command " ++ show c ++
                                      "\nuse :? for help."
          repl
      where
        doType xs = catch doExpr $ \case
            ParseError _ -> doComp
            e -> throwM e
          where
            code = unwords xs
            doExpr = do
              e <- lift $ runParseExpr code
              t <- lift $ typecheckExpr e
              liftIO $ putStrLn $ show e ++ " : " ++ show t

            doComp = do
              cm <- lift $ runParseComputation code
              Res f t c <- lift $ typecheck cm
              let res = normalize (ForallC f t c)
              liftIO $ putStrLn $ show cm ++ " : " ++ show res


    showHelp = liftIO $ do
      putStrLn "help >_<"
      let help = [ ("<statement>", "evaluate/run")
                 , (":l <filename>..", "load file(s)")
                 , (":t <term>", "show the type of <term>")
                 , (":q", "bye bye")
                 , (":?", "show this")
                 , (":! <command>", "run the shell command <command>")]
          res = map (\(a, b) -> nest 4 (text a) $$ nest 30 (text b)) help
      putStrLn $ render (vcat res)

    showContext :: InterpretMonad m => m ()
    showContext = do
      (tm, pctx, cs, os) <- getContext
      liftIO $ putStrLn "context: "
      liftIO $ print tm
      liftIO $ print pctx
      liftIO $ print cs
      liftIO $ print os

    errorHandler :: InterpretMonad m => InterpError -> InputT m ()
    errorHandler err = do
      liftIO $ red' "error: "
      liftIO $ print err

loadfile :: InterpretMonad m => FilePath -> m ()
loadfile fileName = do
  ---------- parsing ----------
  Program decls c <- runParseHmr fileName
  InterpState tmR pctxR csR osR <- ask
  let (tm', cs', os') = nameResolution decls
  liftIO $ modifyIORef' tmR (Map.union (Map.map desugar (Map.fromList tm')))
  liftIO $ modifyIORef' csR (Map.union cs')
  liftIO $ modifyIORef' osR (Map.union os')

  ------------- typechecking -------------
  forM_ tm' $ \(a, b) -> do
    interpLog $ "now inferring: " ++ show a ++ ", " ++ show b
    (_, pctx, _, _) <- getContext
    interpLog $ show pctx
    t <- typecheckExpr b
    interpLog $ "inferred type: " ++ show t
    liftIO $ modifyIORef' pctxR (Map.insert a t)

  (tm, pctx, cs, os) <- getContext
  interpLog "the program is: "
  interpLog $ show c
  interpLog "with context: "
  interpLog $ show tm'
  interpLog $ show pctx
  interpLog $ show cs
  interpLog $ show os

  case c of
    Just c -> do
      --- typechecking the main program ---
      _ <- typecheck c
      interpLog "-------executing---------"
      x <- runComputation c -- TODO
      interpLog "-------result---------"
      liftIO $ print x
    Nothing -> return ()

typecheckExpr :: (Collect a PureType, InterpretMonad m) => a -> m Scheme
typecheckExpr e = do
  Res f a c <- typecheck e
  return $ normalize (Forall f a c)

typecheck :: (-- Show r
               Substitutable r, Collect a r, Garbage r
             , InterpretMonad m)
          => a -> m (InferRes r)
typecheck c = do
  (_, pctx, cs, os) <- getContext
  interpLog $ show pctx
  Res f a cstr <- runInfer c (Context Map.empty pctx) (Signature cs os)
  (s, c) <- runUnify cstr
  ------ perform gc ------
  let t = s ?$ a
      c' = gc c t
  -- liftIO $ red $ "original cons: " ++ show c
  -- liftIO $ green $ "gc cons: " ++ show c'
  let res' = Res (f /\ free t) t (toConsSet c')
  return res'

runComputation :: InterpretMonad m => Computation -> m C.Result
runComputation c = do
  InterpState tmR _ _ _ <- ask
  tm <- liftIO $ readIORef tmR
  let c' = desugar c
  C.exec tm c'

runExpr :: InterpretMonad m => Expr -> m C.Expr
runExpr e = do
  InterpState tmR _ _ _ <- ask
  tm <- liftIO $ readIORef tmR
  let e' = desugar e
  C.runEval tm e'
