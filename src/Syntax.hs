{-
- the frontend language syntax
-}
{-# LANGUAGE OverloadedStrings #-}
module Syntax
  ( Expr(..), Arith(..), BOp(..), UOp(..)
  , Computation(..), Lit(..), OpCase(..), Pattern(..)
  , AST(..), Decl(..), OpDecl(..), TypeTerm(..)
  , traverseOcs
  , TypeEntry(..), ConsSignature, OpSignature
  , nameResolution
  ) where

import Prelude hiding ((<>))
import qualified Data.Text as T
import Text.PrettyPrint
import qualified Data.Map as Map
import Type
import Common
import qualified Data.Set.Monad as Set

data Expr
  = Var Id
  | Lit Lit
  | Abs Id Computation
  | Handler Id PureType Computation OpCase
  -- builtin arithmetrics
  | Arith Arith
  | Cons ConsName [Expr]

-- TODO: Add more
data Arith = BOp BOp Expr Expr | UOp UOp Expr 
data BOp = Add | Sub | Mul | Div | Eq | Lt | Gt | And | Or
  deriving (Show, Eq)
data UOp = Neg | Not
  deriving (Show, Eq)

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
  | OpCall OpTag Expr
  | WithHandle Expr Computation
  | Absurd DirtyType Expr
  | Let Id Expr Computation
  | Do Id Computation Computation
  | DoRec Id Id Computation Computation
  | Case Expr [(Pattern, Computation)]

data Pattern
  = PWild
  | PCons ConsName [Pattern]
  | PVar Id
  -- TODO: Lit?

traverseOcs :: OpCase -> [(OpTag, Id, Id, Computation)]
traverseOcs (Nil _) = []
traverseOcs (OpCase op x k c ocs) = (op, x, k, c) : traverseOcs ocs

instance Show Expr where
  show = render . pp 
instance Show Computation where
  show = render . pp 
instance Show Pattern where
  show = render . pp

data Decl
  = TermDecl Id Expr
  | DataDecl Id [TypeTerm] -- sum of prods
  | EffectDecl Id [OpDecl]

data TypeTerm = TypeTerm ConsName [PureType] -- the constructor & types of the prod
data OpDecl = OpDecl OpTag PureType PureType

data Program = Program [Decl] Computation

type TermMap = Map.Map Id Expr
data TypeEntry = TypeEntry 
                   { retType :: PureType 
                   , arity :: Int
                   , paramType :: [PureType] }
-- signatures for data constructors
-- map from a constructor to its return type, arity and parameter types
type ConsSignature = Map.Map ConsName TypeEntry 
-- signatures for operations
type OpSignature = Map.Map OpTag (PureType, PureType)

nameResolution :: [Decl] -> (TermMap, ConsSignature, OpSignature)
nameResolution [] = (Map.empty, Map.empty, Map.empty)
nameResolution (d:ds) = 
  case d of
    TermDecl x e -> (Map.insert x e tm, cs, os)
    DataDecl x s -> let cs' = Map.fromList (map (f x) s)
                     in (tm, Map.union cs' cs, os)
    -- TODO: what to do with the `eff`?
    EffectDecl eff ops -> let os' = Map.fromList 
                                      (map (\(OpDecl op t1 t2) -> (op, (t1, t2))) ops)
                           in (tm, cs, Map.union os' os)
  where
    (tm, cs, os) = nameResolution ds

    -- process one data constructor entry
    f :: Id -> TypeTerm -> (ConsName, TypeEntry)
    f retTy (TypeTerm cons ts') = (cons, TypeEntry (TCon retTy) (length ts') ts')

    -- get a corresponding function version of the constructor
    -- TODO: after desugaring finished
    -- g :: TypeTerm -> (Id, Expr)
    -- g (TypeTerm cons ts') = (cons, ADT (Cons cons params))
    --   where
    --     params = Var <$> take (length ts') letters

class AST a where
  freeVars :: a -> VarSet

instance AST Expr where
  freeVars (Var x)               = Set.singleton x
  freeVars Lit{}                 = Set.empty
  freeVars (Arith (BOp _ e1 e2)) = freeVars e1 \/ freeVars e2
  freeVars (Arith (UOp _ e))     = freeVars e
  freeVars (Abs x c)             = freeVars c \\ Set.singleton x
  freeVars (Handler x _ c ocs)   = (freeVars c \\ Set.singleton x) \/ freeVars ocs
  freeVars (Cons _ es)               = Set.unions (freeVars <$> es)

instance AST OpCase where
  freeVars Nil{} = Set.empty
  freeVars (OpCase _ x k c ocs) = (freeVars c \\ Set.fromList [x, k]) \/ freeVars ocs

instance AST Computation where
  freeVars (Ret e)                  = freeVars e
  freeVars (App e1 e2)              = freeVars e1 \/ freeVars e2
  freeVars (If e c1 c2)             = freeVars e \/ freeVars c1 \/ freeVars c2
  freeVars (OpCall (OpTag _) e)     = freeVars e
  freeVars (WithHandle h c)         = freeVars h \/ freeVars c
  freeVars (Absurd _ e)             = freeVars e
  freeVars (Let x e c)              = freeVars e \/ (freeVars c \\ Set.singleton x)
  freeVars (Do x c1 c2)             = freeVars c1 \/ (freeVars c2 \\ Set.singleton x)
  freeVars (DoRec f x c1 c2)        = freeVars c1 \/ (freeVars c2 \\ Set.fromList [f, x])
  freeVars (Case e ps) = freeVars e \/ Set.unions (freePat <$> ps)
    where
      freePat :: (Pattern, Computation) -> VarSet
      freePat (p, c) = freeVars c \\ patBinders p

      patBinders :: Pattern -> VarSet
      patBinders PWild = Set.empty
      patBinders (PCons ConsName{} ps) = Set.unions (patBinders <$> ps)
      patBinders (PVar x) = Set.singleton x

instance AST Pattern where
  freeVars PWild = Set.empty
  freeVars (PCons ConsName{} ps) = Set.unions (freeVars <$> ps)
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
  ppr p (Cons (ConsName c) es) = parensIf p $ text' c <+> hsep (parens.ppr 0 <$> es)

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
  ppr p (OpCall (OpTag op) x) = text' op 
    <> parens (pp x)
  ppr p (WithHandle h c) = parensIf p $ "with" <+> ppr 1 h <+> "handle" <+> ppr 1 c
  ppr p (Absurd _ e) = parensIf p $ "absurd" <+> ppr 1 e
  ppr p (Let x e c) = parensIf p $ "let" <+> text' x <+> "=" <+> ppr 1 e <+> "in" <+> ppr 1 c
  ppr p (Do x c1 c2) = parensIf p $ "do" <+> text' x <+> "<-" <+> ppr 1 c1 <+> "in" <+> ppr 1 c2  
  ppr p (DoRec f x c1 c2) = parensIf p $ "do" <+> text' f <+> text' x <+> "<-" <+> pp c1 <+> text "in" <+> ppr 1 c2  
  ppr p (Case e ps) = parensIf p $ "case" <+> ppr 0 e <+> "of" <+> lbrace 
    <+> hsep ((\(p, e) -> ppr 0 p <+> "->" <+> ppr 0 e <> ";") <$> ps) <+> rbrace

instance Pretty Pattern where
  ppr _ PWild = "_"
  ppr p (PCons (ConsName x) ps) = parensIf p $ text' x <+> hsep (ppr 1 <$> ps)
  ppr _ (PVar x) = text' x