{-# LANGUAGE OverloadedStrings #-}
module Core where
import Prelude hiding ((<>))
import qualified Data.Text as T
import qualified Data.Set as Set
import Text.PrettyPrint
import Control.Monad
import Type

type Id = T.Text
type VarSet = Set.Set Id
(\/), (\\) :: VarSet -> VarSet -> VarSet
(\/) = Set.union
(\\) = (Set.\\)

data Expr
  = Var Id
  | Lit Lit
  | Abs Id Computation
  | Handler Id PureType Computation OpCase
  -- builtin arithmetrics
  | Arith Arith

-- TODO: Add more
data Arith = BOp BOp Expr Expr | UOp UOp Expr deriving Show
data BOp = Add | Sub | Mul | Div | Eq | Lt | Gt | And | Or
  deriving Show
data UOp = Neg | Not
  deriving Show

data Lit
  = LInt Int
  | LBool Bool
  | LUnit

data OpCase
  = Nil DirtyType
  | OpCase OpTag Id Id Computation OpCase

data Computation
  = Ret Expr
  | App Expr Expr
  | If Expr Computation Computation
  | OpCall OpTag Expr Id Computation
  | WithHandle Expr Computation
  | Absurd DirtyType Expr
  | Let Id Computation Computation
  | LetRec Id Id Computation Computation

-- the result of evaluation
data Result
  = VRet Expr
  | VOpCall OpTag Expr Id Computation

-- pretty printing AST
class Pretty p where 
  ppr :: Int -> p -> Doc

  pp :: p -> Doc
  pp = ppr 0

parensIf :: Int -> Doc -> Doc 
parensIf i = if i /= 0 then parens else id

text' :: Id -> Doc
text' = text . T.unpack

instance Pretty Lit where
  ppr _ l = case l of 
              LInt i -> int i
              LBool b -> text (show b)
              LUnit -> text "()"

instance Pretty Expr where
  ppr _ (Lit l) = pp l
  ppr _ (Var x) = text' x
  ppr p (Abs x a) = parensIf p $ char '\\' <>  text' x <+> "." <+> pp a
  ppr p (Handler x _ c ocs) = parensIf p $ "handler" <+> braces body
      where body = "return" <+> text' x <+> "->" <+> pp c <> comma <+> pp ocs
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

instance Pretty OpCase where 
  ppr _ Nil{} = empty
  ppr _ (OpCase (OpTag op) x k c ocs) = 
        text (T.unpack op)
    <>  parens (text' x <> semi <> text' k) 
    <+> "->" <+> pp c <+> semi <+> pp ocs

instance Pretty Computation where 
  ppr p (Ret e) = parensIf p $ "return" <+> ppr (p+1) e
  ppr p (App a b) = parensIf p $ ppr 1 a <+> ppr 1 b
  ppr p (If e c1 c2) = parensIf p $
      "if" <+> pp e <+> "then" <+> pp c1 <+> "else" <+> pp c2
  ppr p (OpCall (OpTag op) x y c) = text' op 
    <> parens (pp x <> semi <+> text' y <> char '.' <+> pp c)
  ppr p (WithHandle h c) = parensIf p $ "with" <+> ppr 1 h <+> "handle" <+> ppr 1 c
  ppr p (Absurd _ e) = parensIf p $ "absurd" <+> ppr 1 e
  ppr p (Let x c1 c2) = parensIf p $ "let" <+> text' x <+> text "<-" <+> ppr 1 c1 <+> text "in" <+> ppr 1 c2  
  ppr p (LetRec f x c1 c2) = parensIf p $ "let" <+> text' f <+> text' x <+> "<-" <+> pp c1 <+> text "in" <+> ppr 1 c2  

instance Show Expr where
  show = render . pp 
instance Show Computation where
  show = render . pp 

instance Show Result where
  show (VRet e) = render (pp (Ret e))
  show (VOpCall op x y c) = render (pp (OpCall op x y c))

freshNames :: VarSet -> [Id]
freshNames s = filter (`Set.notMember` s) letters
freshName :: VarSet -> Id
freshName = head . freshNames
letters :: [Id]
letters = map T.pack $ [1..] >>= flip replicateM ['a'..'z']

class AST a where
  freeVars :: a -> VarSet
  binders :: a -> VarSet
  rename :: VarSet -> (Id, Id) -> a -> a
  -- names can only bind expressions
  substitute :: (Id, Expr) -> a -> a

instance AST Expr where
  freeVars (Var x)               = Set.singleton x
  freeVars Lit{}                 = Set.empty
  freeVars (Arith (BOp _ e1 e2)) = freeVars e1 \/ freeVars e2
  freeVars (Arith (UOp _ e))     = freeVars e
  freeVars (Abs x c)             = freeVars c \\ Set.singleton x
  freeVars (Handler x _ c ocs)   = (freeVars c \\ Set.singleton x) \/ freeVars ocs

  binders (Var x)               = Set.empty
  binders Lit{}                 = Set.empty
  binders (Arith (BOp _ e1 e2)) = binders e1 \/ binders e2
  binders (Arith (UOp _ e))     = binders e
  binders (Abs x c)             = binders c \/ Set.singleton x
  binders (Handler x _ c ocs)   = (binders c \/ Set.singleton x) \/ freeVars ocs

  rename bindVars (a, b) (Var x) | Set.notMember x bindVars && x == a = Var b
                                 | otherwise = Var x
  rename _ _ l@Lit{} = l 
  rename bindVars s (Arith (BOp op e1 e2)) = Arith (BOp op (rename bindVars s e1) (rename bindVars s e2))
  rename bindVars s (Arith (UOp op e)) = Arith (UOp op (rename bindVars s e))
  rename bindVars s (Abs x c) = Abs x (rename (Set.insert x bindVars) s c)
  rename bindVars s (Handler x a c ocs) = Handler x a (rename (Set.insert x bindVars) s c) (rename bindVars s ocs)

  substitute (y, n) (Var x) | x == y = n
                            | otherwise = Var x
  substitute _ l@Lit{} = l
  substitute s (Arith (BOp op e1 e2)) = Arith (BOp op (substitute s e1) (substitute s e2))
  substitute s (Arith (UOp op e)) = Arith (UOp op (substitute s e))
  substitute (x, n) (Abs y p) = let z = freshName (Set.insert x (freeVars n) \/ freeVars p \/ binders p) 
                                 in Abs z (substitute (x, n) (rename Set.empty (y, z) p))
  substitute (x, n) (Handler y a c ocs) = let z = freshName (Set.insert x (freeVars n) \/ freeVars c \/ binders c)
                                           in Handler z a (substitute (x, n) (rename Set.empty (y, z) c))
                                                          (substitute (x, n) ocs)

instance AST OpCase where
  freeVars Nil{} = Set.empty
  freeVars (OpCase _ x k c ocs) = (freeVars c \\ Set.fromList [x, k]) \/ freeVars ocs

  binders Nil{} = Set.empty
  binders (OpCase _ x k c ocs) = (binders c \/ Set.fromList [x, k]) \/ binders ocs

  rename _ _ n@Nil{} = n
  rename bindVars s (OpCase op x k c ocs) = OpCase op x k (rename (bindVars \/ Set.fromList [x, k]) s c) 
                                                          (rename bindVars s ocs)

  substitute _ n@Nil{} = n
  substitute (x, n) (OpCase op y k c ocs) = let fvs = Set.insert x (freeVars n) \/ freeVars c \/ binders c
                                                [a, b] = take 2 (freshNames fvs)
                                                c' = rename Set.empty (y, a) . rename Set.empty (k, b) $ c
                                             in OpCase op a b (substitute (x, n) c') (substitute (x, n) ocs)

instance AST Computation where
  freeVars (Ret e)                  = freeVars e
  freeVars (App e1 e2)              = freeVars e1 \/ freeVars e2
  freeVars (If e c1 c2)             = freeVars e \/ freeVars c1 \/ freeVars c2
  freeVars (OpCall (OpTag _) e y c) = freeVars e \/ (freeVars c \\ Set.singleton y)
  freeVars (WithHandle h c)         = freeVars h \/ freeVars c
  freeVars (Absurd _ e)             = freeVars e
  freeVars (Let x c1 c2)            = freeVars c1 \/ (freeVars c2 \\ Set.singleton x)
  freeVars (LetRec f x c1 c2)       = freeVars c1 \/ (freeVars c2 \\ Set.fromList [f, x])

  binders (Ret e)                  = binders e
  binders (App e1 e2)              = binders e1 \/ binders e2
  binders (If e c1 c2)             = binders e \/ binders c1 \/ binders c2
  binders (OpCall (OpTag _) e y c) = binders e \/ (binders c \/ Set.singleton y)
  binders (WithHandle h c)         = binders h \/ binders c
  binders (Absurd _ e)             = binders e
  binders (Let x c1 c2)            = binders c1 \/ (binders c2 \/ Set.singleton x)
  binders (LetRec f x c1 c2)       = binders c1 \/ (binders c2 \/ Set.fromList [f, x])

  rename bindVars s cm = 
    case cm of
      Ret e            -> Ret (rename' e)
      App e1 e2        -> App (rename' e1) (rename' e2)
      If e c1 c2       -> If (rename' e) (rename' c1) (rename' c2)
      OpCall op e y c  -> OpCall op (rename' e) y (renameWith (Set.insert y bindVars) c)
      WithHandle h c   -> WithHandle (rename' h) (rename' c)
      Absurd t e       -> Absurd t (rename' e)
      Let x c1 c2      -> Let x (rename' c1) (renameWith (Set.insert x bindVars) c2)
      LetRec f x c1 c2 -> LetRec f x (rename' c1) (renameWith (bindVars \/ Set.fromList [f, x]) c2)                          
    where
      rename' :: AST a => a -> a
      rename' = rename bindVars s 
      renameWith v = rename v s
  
  substitute s@(x, n) cm =
    case cm of
      Ret e            -> Ret (subst' e)
      App e1 e2        -> App (subst' e1) (subst' e2)
      If e c1 c2       -> If (subst' e) (subst' c1) (subst' c2)
      OpCall op e y c  -> let z = freshName (Set.insert x (freeVars n) \/ freeVars c \/ binders c)
                           in OpCall op (subst' e) z (subst' (rename Set.empty (y, z) c))
      WithHandle h c   -> WithHandle (subst' h) (subst' c)
      Absurd t e       -> Absurd t (subst' e)
      -- TODO: Is the `freeVars c1` necessary?
      Let y c1 c2      -> let z = freshName (Set.insert x (freeVars n) \/ freeVars c2 \/ binders c2 \/ freeVars c1)
                           in Let z (subst' c1) (subst' (rename Set.empty (y, z) c2))
      LetRec f y c1 c2 -> let fvs = Set.insert x (freeVars n) \/ freeVars c2 \/ binders c2 \/ freeVars c1
                              [a, b] = take 2 (freshNames fvs)
                           in LetRec a b (subst' c1) 
                                         (subst' (rename Set.empty (f, a) . rename Set.empty (y, b) $ c2))
    where
      subst' :: AST a => a -> a
      subst' = substitute s

exec' :: Computation -> Result
-- TODO: Is this correct?
exec' (Ret e) = VRet (eval e)
exec' (OpCall op e x c) = VOpCall op e x c
exec' (If e c1 c2) = case eval e of 
                      Lit (LBool True)  -> exec' c1
                      Lit (LBool False) -> exec' c2
                      _                 -> error "if condition mismatch"
exec' Absurd{} = error "never execute absurd"

exec' (App (Abs x c) e) = exec' (substitute (x, e) c)
exec' App{} = error "not a function"
exec' (Let x c1 c2) = case exec' c1 of
                            VRet e -> exec' (substitute (x, e) c2)
                            VOpCall op e y c -> VOpCall op e y (Let x c c2)
exec' (WithHandle h@(Handler xv a cv ocs) oc) =
    case exec' oc of
      VRet e -> exec' (substitute (xv, e) cv)
      VOpCall op e y c -> case lookupCase op ocs of
                            Just (xi, ki, ci) -> 
                              exec' (substitute (xi, e) . substitute (ki, Abs y (WithHandle h c)) $ ci)
                            Nothing -> VOpCall op e y (WithHandle h c)
  where
    lookupCase :: OpTag -> OpCase -> Maybe (Id, Id, Computation)
    lookupCase _ Nil{} = Nothing
    lookupCase op (OpCase op' x k c ocs) | op == op' = Just (x, k, c)
                                         | otherwise = lookupCase op ocs
exec' WithHandle{} = error "not a handler"
exec' (LetRec f x c1 c2) = undefined

-- builtin evaluation
eval :: Expr -> Expr
eval (Arith a) = Lit res
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
eval x = x
