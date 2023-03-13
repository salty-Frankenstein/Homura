{-
- the frontend language syntax
-}
{-# LANGUAGE OverloadedStrings #-}
module Syntax where

import Prelude hiding ((<>))
import qualified Data.Text as T
import Text.PrettyPrint
import qualified Data.Map as Map
import Type
import Common
import qualified Data.Set as Set

data Expr
  = Var Id
  | Lit Lit
  | Abs Id Computation
  | Handler Id PureType Computation OpCase
  -- builtin arithmetrics
  | Arith Arith
  | ADT ADT

-- algebraic data types
data ADT
  = Inl Expr
  | Inr Expr 
  | Prod Expr Expr 
  | Fold Expr 
  | Cons Id [Expr]
  | Unfold Expr 

-- TODO: Add more
data Arith = BOp BOp Expr Expr | UOp UOp Expr 
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
  | Case Expr [(Pattern, Computation)]

data Pattern
  = PWild
  | PCons Id [Pattern]
  | PVar Id
  -- TODO: Lit?

instance Show Expr where
  show = render . pp 
instance Show Computation where
  show = render . pp 
instance Show Pattern where
  show = render . pp

data Decl
  = TermDecl Id Expr
  | DataDecl Id [TypeTerm] -- sum of prods

data TypeTerm = TypeTerm Id [Id] -- the constructor & types of the prod

data Program = Program [Decl] Computation

type TermMap = Map.Map Id Expr
type TypeMap = Map.Map Id PureType

nameResolution :: [Decl] -> (TermMap, TypeMap)
nameResolution [] = (Map.empty, Map.empty)
nameResolution (d:ds) = 
  case d of
    TermDecl x e -> (Map.insert x e tm, ty)
    DataDecl x s -> let (ty', ts) = toSum s
                     in (tm, Map.insert x ts (Map.union ty ty'))
  where
    (tm, ty) = nameResolution ds

    -- since declaration of ADTs will introduce constructors
    -- it will return a map from constructor names to the type related
    -- during the process
    toSum :: [TypeTerm] -> (TypeMap, PureType)
    toSum [] = (Map.empty, typeBottom)  -- TODO: check this
    toSum [TypeTerm x types] = let res = toProd types
                                in (Map.singleton x res, res)
    toSum (TypeTerm x types:xs) = let (tm, t) = toSum xs
                                      res = toProd types
                                   in (Map.insert x res tm, TSum res t)

    toProd :: [Id] -> PureType
    toProd [] = typeTop
    toProd [x] = TCon x
    toProd (x:xs) = TProd (TCon x) (toProd xs)

afold :: (Expr -> VarSet) -> ADT -> VarSet
afold f t = case t of
  Inl e -> f e
  Inr e -> f e 
  Prod e1 e2 -> f e1 \/ f e2
  Cons _ es -> Set.unions (f <$> es)
  Fold e -> f e
  Unfold e -> f e

class AST a where
  freeVars :: a -> VarSet

instance AST Expr where
  freeVars (Var x)               = Set.singleton x
  freeVars Lit{}                 = Set.empty
  freeVars (Arith (BOp _ e1 e2)) = freeVars e1 \/ freeVars e2
  freeVars (Arith (UOp _ e))     = freeVars e
  freeVars (Abs x c)             = freeVars c \\ Set.singleton x
  freeVars (Handler x _ c ocs)   = (freeVars c \\ Set.singleton x) \/ freeVars ocs
  freeVars (ADT t)               = afold freeVars t

instance AST OpCase where
  freeVars Nil{} = Set.empty
  freeVars (OpCase _ x k c ocs) = (freeVars c \\ Set.fromList [x, k]) \/ freeVars ocs

instance AST Computation where
  freeVars (Ret e)                  = freeVars e
  freeVars (App e1 e2)              = freeVars e1 \/ freeVars e2
  freeVars (If e c1 c2)             = freeVars e \/ freeVars c1 \/ freeVars c2
  freeVars (OpCall (OpTag _) e y c) = freeVars e \/ (freeVars c \\ Set.singleton y)
  freeVars (WithHandle h c)         = freeVars h \/ freeVars c
  freeVars (Absurd _ e)             = freeVars e
  freeVars (Let x c1 c2)            = freeVars c1 \/ (freeVars c2 \\ Set.singleton x)
  freeVars (LetRec f x c1 c2)       = freeVars c1 \/ (freeVars c2 \\ Set.fromList [f, x])
  freeVars (Case e ps) = freeVars e \/ Set.unions (freePat <$> ps)
    where
      freePat :: (Pattern, Computation) -> VarSet
      freePat (p, c) = freeVars c \\ patBinders p

      patBinders :: Pattern -> VarSet
      patBinders PWild = Set.empty
      patBinders (PCons x ps) = Set.singleton x \/ Set.unions (patBinders <$> ps)
      patBinders (PVar x) = Set.singleton x

instance AST Pattern where
  freeVars PWild = Set.empty
  freeVars (PCons x ps) = Set.singleton x \/ Set.unions (freeVars <$> ps)
  freeVars (PVar x) = Set.singleton x

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
  ppr p (ADT t) = parensIf p $ case t of
    Inl x -> "Inl" <+> ppr 1 x
    Inr x -> "Inr" <+> ppr 1 x
    Prod x1 x2 -> char '<' <> ppr 0 x1 <> comma <+> ppr 0 x2 <> char '>'
    Cons c es -> text' c <+> parens (hsep (ppr 0 <$> es))
    Fold x -> "fold" <+> ppr 1 x
    Unfold x -> "unfold" <+> ppr 1 x 

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
  ppr p (Case e ps) = parensIf p $ "case" <+> ppr 0 e <+> "of" <+> lbrace 
    <+> hsep ((\(p, e) -> ppr 0 p <+> "->" <+> ppr 0 e <> ";") <$> ps) <+> rbrace

instance Pretty Pattern where
  ppr _ PWild = "_"
  ppr p (PCons x ps) = parensIf p $ text' x <+> hsep (ppr 1 <$> ps)
  ppr _ (PVar x) = text' x