{-# LANGUAGE OverloadedStrings #-}
module Core 
  ( Expr(..), Arith(..), BOp(..), UOp(..)
  , Computation(..), Lit(..), OpCase(..), Result(..)
  , exec, ExecError(..), TermMap
  ) where

import Text.PrettyPrint
import Type
import Common
import Utils.Pretty
import Prelude hiding ((<>))
import qualified Data.Set.Monad as Set
import qualified Data.Map as Map
import Control.Monad.Reader
import Control.Monad.Except
import qualified Debug.Trace as DT
trace s a = DT.trace (s ++ "\n") a

data Expr
  = Var Id
  | Lit Lit
  | Abs Id Computation
  | Handler Id PureType Computation OpCase
  -- builtin arithmetrics
  | Arith Arith
  | Cons ConsName [Expr]
  deriving Eq

-- TODO: Add more
data Arith = BOp BOp Expr Expr | UOp UOp Expr deriving (Show, Eq)
data BOp = Add | Sub | Mul | Div | Eq | Lt | Gt | And | Or
  deriving (Show, Eq)
data UOp = Neg | Not
  deriving (Show, Eq)

data Lit
  = LInt Int
  | LBool Bool
  | LUnit
  deriving Eq

data OpCase
  = Nil DirtyType
  | OpCase OpTag Id Id Computation OpCase
  deriving Eq

data Computation
  = Ret Expr
  | App Expr Expr
  | If Expr Computation Computation
  | OpCall OpTag Expr Id Computation
  | WithHandle Expr Computation
  | Absurd DirtyType Expr
  | Let Id Expr Computation
  | Do Id Computation Computation
  | DoRec Id Id Computation Computation
  | Case Expr ConsName [Id] Computation Computation
  deriving Eq

-- the result of evaluation
data Result
  = VRet Expr
  | VOpCall OpTag Expr Id Computation
  deriving Eq

-- pretty printing AST
instance Pretty Lit where
  ppr _ l = case l of
              LInt i -> int i
              LBool b -> text (show b)
              LUnit -> text "()"

instance Pretty Expr where
  ppr _ (Lit l) = pp l
  ppr _ (Var x) = text x
  ppr p (Abs x a) = parensIf p $ char '\\' <>  text x <+> "." <+> pp a
  ppr p (Handler x _ c ocs) = parensIf p $ "handler" <+> braces body
      where body = "return" <+> text x <+> "->" <+> pp c <> comma <+> pp ocs
  ppr p (Arith a) = parensIf p body
    where
      body = case a of
               BOp bop v1 v2 ->
                 case bop of
                   Add -> pp v1 <+> char '+' <+> pp v2
                   Sub -> pp v1 <+> char '-' <+> pp v2
                   Mul -> pp v1 <+> char '*' <+> pp v2
                   Div -> pp v1 <+> char '/' <+> pp v2
                   Eq  -> pp v1 <+> text "==" <+> pp v2
                   Lt  -> pp v1 <+> text "<" <+> pp v2
                   Gt  -> pp v1 <+> text ">" <+> pp v2
                   And -> pp v1 <+> text "&&" <+> pp v2
                   Or  -> pp v1 <+> text "||" <+> pp v2
               UOp uop v ->
                 case uop of
                   Neg -> text "-" <+> pp v
                   Not -> text "!" <+> pp v
  ppr p (Cons (ConsName c) es) = parensIf p $ text c <+> parens (hsep (ppr 0 <$> es))

instance Pretty OpCase where
  ppr _ Nil{} = empty
  ppr _ (OpCase (OpTag op) x k c ocs) =
        text op
    <>  parens (text x <> semi <> text k)
    <+> "->" <+> pp c <+> semi <+> pp ocs

instance Pretty Computation where
  ppr p (Ret e) = parensIf p $ "return" <+> ppr (p+1) e
  ppr p (App a b) = parensIf p $ ppr 1 a <+> ppr 1 b
  ppr p (If e c1 c2) = parensIf p $
      "if" <+> pp e <+> "then" <+> pp c1 <+> "else" <+> pp c2
  ppr p (OpCall (OpTag op) x y c) = text op
    <> parens (pp x <> semi <+> text y <> char '.' <+> pp c)
  ppr p (WithHandle h c) = parensIf p $ "with" <+> ppr 1 h <+> "handle" <+> ppr 1 c
  ppr p (Absurd _ e) = parensIf p $ "absurd" <+> ppr 1 e
  ppr p (Let x e c) = parensIf p $ "let" <+> text x <+> "=" <+> ppr 1 e <+> "in" <+> ppr 1 c
  ppr p (Do x c1 c2) = parensIf p $ "do" <+> text x <+> "<-" <+> ppr 1 c1 <+> "in" <+> ppr 1 c2
  ppr p (DoRec f x c1 c2) = parensIf p $ "do" <+> text f <+> text x <+> "<-" <+> pp c1 <+> "in" <+> ppr 1 c2
  ppr p (Case e (ConsName cons) vs c1 c2) = parensIf p $ "case" <+> ppr 0 e <+> "of" <+> lbrace
    <+> text cons <+> hsep (text <$> vs) <+> "->" <+> ppr 0 c1
    <+> ";" <+> "_ ->" <+> ppr 0 c2 <+> rbrace

instance Show Expr where
  show = render . pp
instance Show Computation where
  show = render . pp
instance Show OpCase where
  show = render . pp

instance Show Result where
  show (VRet e) = render (pp (Ret e))
  show (VOpCall op x y c) = render (pp (OpCall op x y c))

class AST a where
  freeVars :: a -> VarSet
  binders :: a -> VarSet
  rename :: VarSet -> (Id, Id) -> a -> a
  -- names can only bind expressions
  substitute :: VarSet -> (Id, Expr) -> a -> a

instance AST Expr where
  freeVars (Var x)               = Set.singleton x
  freeVars Lit{}                 = Set.empty
  freeVars (Arith (BOp _ e1 e2)) = freeVars e1 \/ freeVars e2
  freeVars (Arith (UOp _ e))     = freeVars e
  freeVars (Abs x c)             = freeVars c \\ Set.singleton x
  freeVars (Handler x _ c ocs)   = (freeVars c \\ Set.singleton x) \/ freeVars ocs
  freeVars (Cons _ es)           = Set.unions (freeVars <$> es)

  binders (Var x)               = Set.empty
  binders Lit{}                 = Set.empty
  binders (Arith (BOp _ e1 e2)) = binders e1 \/ binders e2
  binders (Arith (UOp _ e))     = binders e
  binders (Abs x c)             = binders c \/ Set.singleton x
  binders (Handler x _ c ocs)   = (binders c \/ Set.singleton x) \/ binders ocs
  binders (Cons _ es)           = Set.unions (binders <$> es)

  rename bindVars (a, b) (Var x) | Set.notMember x bindVars && x == a = Var b
                                 | otherwise = Var x
  rename _ _ l@Lit{} = l
  rename bindVars s (Arith (BOp op e1 e2)) = Arith (BOp op (rename bindVars s e1) (rename bindVars s e2))
  rename bindVars s (Arith (UOp op e)) = Arith (UOp op (rename bindVars s e))
  rename bindVars s (Abs x c) = Abs x (rename (Set.insert x bindVars) s c)
  rename bindVars s (Handler x a c ocs) = Handler x a (rename (Set.insert x bindVars) s c) (rename bindVars s ocs)
  rename bindVars s (Cons c es) = Cons c (rename bindVars s <$> es)

  substitute bv (y, n) (Var x) | x == y = n
                               | otherwise = Var x
  substitute bv _ l@Lit{} = l
  substitute bv s (Arith (BOp op e1 e2)) = Arith (BOp op (substitute bv s e1) (substitute bv s e2))
  substitute bv s (Arith (UOp op e)) = Arith (UOp op (substitute bv s e))
  substitute bv (x, n) (Abs y p) = let z = freshName (Set.insert x (freeVars n) \/ freeVars p \/ binders p \/ bv)
                                    in Abs z (substitute (Set.insert z bv) (x, n) (rename Set.empty (y, z) p))
  substitute bv (x, n) (Handler y a c ocs) = let z = freshName (Set.insert x (freeVars n) \/ freeVars c \/ binders c \/ bv)
                                              in Handler z a (substitute (Set.insert z bv) (x, n) (rename Set.empty (y, z) c))
                                                             (substitute bv (x, n) ocs)
  substitute bv s (Cons c es) = Cons c (substitute bv s <$> es)

instance AST OpCase where
  freeVars Nil{} = Set.empty
  freeVars (OpCase _ x k c ocs) = (freeVars c \\ Set.fromList [x, k]) \/ freeVars ocs

  binders Nil{} = Set.empty
  binders (OpCase _ x k c ocs) = (binders c \/ Set.fromList [x, k]) \/ binders ocs

  rename _ _ n@Nil{} = n
  rename bindVars s (OpCase op x k c ocs) = OpCase op x k (rename (bindVars \/ Set.fromList [x, k]) s c)
                                                          (rename bindVars s ocs)

  substitute _ _ n@Nil{} = n
  substitute bv (x, n) (OpCase op y k c ocs) = let fvs = Set.insert x (freeVars n) \/ freeVars c \/ binders c \/ bv \/ Set.fromList [y,k]
                                                   [a, b] = take 2 (freshNames fvs)
                                                   c' = rename Set.empty (y, a) . rename Set.empty (k, b) $ c
                                                in OpCase op a b (substitute (bv \/ Set.fromList [a, b]) (x, n) c') (substitute bv (x, n) ocs)

instance AST Computation where
  freeVars (Ret e)                  = freeVars e
  freeVars (App e1 e2)              = freeVars e1 \/ freeVars e2
  freeVars (If e c1 c2)             = freeVars e \/ freeVars c1 \/ freeVars c2
  freeVars (OpCall (OpTag _) e y c) = freeVars e \/ (freeVars c \\ Set.singleton y)
  freeVars (WithHandle h c)         = freeVars h \/ freeVars c
  freeVars (Absurd _ e)             = freeVars e
  freeVars (Let x e c)              = freeVars c \/ (freeVars e \\ Set.singleton x)
  freeVars (Do x c1 c2)             = freeVars c1 \/ (freeVars c2 \\ Set.singleton x)
  freeVars (DoRec f x c1 c2)        = freeVars c1 \/ (freeVars c2 \\ Set.fromList [f, x])
  freeVars (Case e _ vs c1 c2)   = freeVars e \/ (freeVars c1 \\ Set.fromList vs) \/ freeVars c2

  binders (Ret e)                  = binders e
  binders (App e1 e2)              = binders e1 \/ binders e2
  binders (If e c1 c2)             = binders e \/ binders c1 \/ binders c2
  binders (OpCall (OpTag _) e y c) = binders e \/ (binders c \/ Set.singleton y)
  binders (WithHandle h c)         = binders h \/ binders c
  binders (Absurd _ e)             = binders e
  binders (Let x e c)              = binders c \/ (binders e \/ Set.singleton x)
  binders (Do x c1 c2)             = binders c1 \/ (binders c2 \/ Set.singleton x)
  binders (DoRec f x c1 c2)        = binders c1 \/ (binders c2 \/ Set.fromList [f, x])
  binders (Case e _ vs c1 c2)      = binders e \/ binders c1 \/ binders c2 \/ Set.fromList vs

  rename bindVars s cm =
    case cm of
      Ret e             -> Ret (rename' e)
      App e1 e2         -> App (rename' e1) (rename' e2)
      If e c1 c2        -> If (rename' e) (rename' c1) (rename' c2)
      OpCall op e y c   -> OpCall op (rename' e) y (renameWith (Set.insert y bindVars) c)
      WithHandle h c    -> WithHandle (rename' h) (rename' c)
      Absurd t e        -> Absurd t (rename' e)
      Let x e c         -> Let x (rename' e) (renameWith (Set.insert x bindVars) c)
      Do x c1 c2        -> Do x (rename' c1) (renameWith (Set.insert x bindVars) c2)
      DoRec f x c1 c2   -> DoRec f x (renameWith (bindVars \/ Set.fromList [f, x]) c1) 
                                     (renameWith (Set.insert f bindVars) c2)
      Case e c vs c1 c2 -> Case (rename' e) c vs (renameWith (bindVars \/ Set.fromList vs) c1) (rename' c2)
    where
      rename' :: AST a => a -> a
      rename' = rename bindVars s
      renameWith v = rename v s

  substitute bv s@(x, n) cm =
    case cm of
      Ret e             -> Ret (subst' e)
      App e1 e2         -> App (subst' e1) (subst' e2)
      If e c1 c2        -> If (subst' e) (subst' c1) (subst' c2)
      OpCall op e y c   -> let z = freshName (Set.insert x (freeVars n) \/ freeVars c \/ binders c \/ bv)
                            in OpCall op (subst' e) z (substWith (Set.insert z bv) (rename Set.empty (y, z) c))
      WithHandle h c    -> WithHandle (subst' h) (subst' c)
      Absurd t e        -> Absurd t (subst' e)
      Let y e c         -> let z = freshName (Set.insert x (freeVars n) \/ freeVars c \/ binders c \/ freeVars e \/ bv)
                            in Let z (subst' e) (substWith (Set.insert z bv) (rename Set.empty (y, z) c))
      -- TODO: Is the freeVars c1` necessary?
      Do y c1 c2        -> let z = freshName (Set.insert x (freeVars n) \/ freeVars c2 \/ binders c2 \/ freeVars c1 \/ bv)
                            in Do z (subst' c1) (substWith (Set.insert z bv) (rename Set.empty (y, z) c2))
      DoRec f y c1 c2   -> let fvs = Set.insert x (freeVars n) \/ freeVars c2 \/ binders c2 \/ freeVars c1 \/ binders c1 \/ bv \/ Set.fromList [f, y]
                               [a, b] = take 2 (freshNames fvs)
                            in DoRec a b (substWith (bv \/ Set.fromList [a, b]) (rename Set.empty (f, a) . rename Set.empty (y, b) $ c1))
                                         (substWith (Set.insert f bv) (rename Set.empty (f, a) c2))
      Case e c vs c1 c2 -> let fvs = Set.insert x (freeVars n) \/ freeVars c1 \/ binders c1 \/ bv
                               newvars = take (length vs) (freshNames fvs)
                            in Case (subst' e) c newvars (substWith (bv \/ Set.fromList newvars) (foldr ($) c1 (rename Set.empty <$> zip vs newvars)))
                                    (subst' c2)
    where
      subst' :: AST a => a -> a
      subst' = substitute bv s
      substWith b = substitute b s

type TermMap = Map.Map Id Expr
type ExecM = ExceptT ExecError (Reader TermMap)
data ExecError = UndefinedVariable Id
               | IfConditionMismatch Expr
               | ApplyNonFunction Expr
               | ApplyNonHandler
               deriving Eq

instance Show ExecError where
  show (UndefinedVariable v) = "undefined variable: " ++ v
  show (IfConditionMismatch e) = "if condition mismatch: " ++ show e
  show (ApplyNonFunction f) = "not a function: " ++ show f
  show ApplyNonHandler = "not a handler"

exec :: TermMap -> Computation -> Either ExecError Result
exec ctx c = runReader (runExceptT (exec' c)) ctx

exec' :: Computation -> ExecM Result
-- TODO: Is this correct?
exec' (Ret e) = VRet <$> eval e
exec' (OpCall op e x c) = return $ VOpCall op e x c
exec' (If e c1 c2) = do
    res <- eval e
    case res of
      Lit (LBool True)  -> exec' c1
      Lit (LBool False) -> exec' c2
      _                 -> throwError (IfConditionMismatch e)
exec' Absurd{} = error "never execute absurd"

exec' (App (Abs x c) e) = exec' (substitute Set.empty (x, e) c)
exec' (App v@(Var _) e) = do
  res <- eval v 
  exec' (App res e)
exec' a@(App e _) = throwError (ApplyNonFunction e)
exec' (Let x e c) = do
    res <- eval e
    exec' (substitute Set.empty (x, res) c)
exec' t@(Do x c1 c2) = do
    res <- exec' c1
    case res of
      VRet e -> exec' (substitute Set.empty (x, e) c2)
      VOpCall op e y c -> return $ VOpCall op e y (Do x c c2)
exec' t@(WithHandle h@(Handler xv a cv ocs) oc) = do
    res <- exec' oc
    case res of
      VRet e -> exec' (substitute Set.empty (xv, e) cv)
      VOpCall op e y c -> case lookupCase op ocs of
                            Just (xi, ki, ci) ->
                              exec' (substitute Set.empty (xi, e) . substitute Set.empty (ki, Abs y (WithHandle h c)) $ ci)
                            Nothing -> return $ VOpCall op e y (WithHandle h c)
  where
    lookupCase :: OpTag -> OpCase -> Maybe (Id, Id, Computation)
    lookupCase _ Nil{} = Nothing
    lookupCase op (OpCase op' x k c ocs) | op == op' = Just (x, k, c)
                                         | otherwise = lookupCase op ocs
exec' (WithHandle h c) = do
  x <- eval h
  exec' (WithHandle x c)
exec' WithHandle{} = throwError ApplyNonHandler
exec' (DoRec f x c1 c2) = exec' $ substitute Set.empty (f, Abs x (DoRec f x c1 c1)) c2
exec' (Case e c vs c1 c2) = do
    res <- eval e
    case res of
      Cons c' vs' -> if c == c' 
        then exec' (foldr ($) c1 (substitute Set.empty <$> zip vs vs'))
            -- error $ "\n debug: " ++ show (Case e c vs c1 c2)
        else exec' c2
      t -> error $ "pattern mismatch: " ++ show t
                ++ "\n debug: "
                ++ show (Case e c vs c1 c2)

-- builtin evaluation
eval :: Expr -> ExecM Expr
eval (Var x) = do
  ctx <- lift ask
  case Map.lookup x ctx of
    Just e -> return e
    Nothing -> throwError (UndefinedVariable x)
eval (Arith a) = return $ Lit res
  where
    res = case a of
            BOp Add (Lit (LInt i1))  (Lit (LInt i2))  -> LInt (i1 + i2)
            BOp Sub (Lit (LInt i1))  (Lit (LInt i2))  -> LInt (i1 - i2)
            BOp Mul (Lit (LInt i1))  (Lit (LInt i2))  -> LInt (i1 * i2)
            BOp Div (Lit (LInt i1))  (Lit (LInt i2))  -> LInt (div i1 i2)
            BOp Eq  (Lit (LInt i1))  (Lit (LInt i2))  -> LBool (i1 == i2)
            BOp Lt  (Lit (LInt i1))  (Lit (LInt i2))  -> LBool (i1 < i2)
            BOp Gt  (Lit (LInt i1))  (Lit (LInt i2))  -> LBool (i1 > i2)
            BOp And (Lit (LBool b1)) (Lit (LBool b2)) -> LBool (b1 && b2)
            BOp Or  (Lit (LBool b1)) (Lit (LBool b2)) -> LBool (b1 || b2)
            UOp Neg (Lit (LInt i)) -> LInt (- i)
            UOp Not (Lit (LBool b)) -> LBool (not b)
            _ -> error $ "mismatch: " ++ show a
eval (Cons c es) = Cons c <$> mapM eval es
eval x = return x
