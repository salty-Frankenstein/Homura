module Parser where

import Common
import Syntax
import Lib.Arith
import Type
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Language
import qualified Text.Parsec.Token as T
import Control.Monad.Identity
import qualified Data.Set.Monad as Set

reservedNames, reservedOpNames :: [String]
reservedNames = ["handler", "pure", "if", "then", "else"
                , "True", "False", "with", "handle"
                , "absurd", "let", "do", "letrec", "case", "of"
                , "data", "effect", "main"]
reservedOpNames = ["+", "-", "*", "/", "==", "&&", "||"
                  , "->", "=>", "|", "=", ":", "()"]
hmrDef = T.LanguageDef
          { T.commentStart    = "{-"
          , T.commentEnd      = "-}"
          , T.commentLine     = "--"
          , T.nestedComments  = True
          , T.identStart      = T.identStart haskellStyle
          , T.identLetter     = T.identLetter haskellStyle
          , T.opStart         = T.opStart haskellStyle
          , T.opLetter        = T.opLetter haskellStyle
          , T.reservedNames   = reservedNames
          , T.reservedOpNames = reservedOpNames
          , T.caseSensitive   = True }

lexer :: T.GenTokenParser String u Identity
lexer = T.makeTokenParser hmrDef

allID :: Parser String
allID = T.identifier lexer
identifier :: Parser String
identifier = try (lookAhead lower) >> allID
typeId :: Parser String
typeId = try (lookAhead upper) >> allID

param :: Parser String
param = identifier <|> (reservedOp "_" >> return "_")
semi = T.semi lexer
-- comma = T.comma lexer

whiteSpace = T.whiteSpace lexer
semiSep = T.semiSep lexer
commaSep = T.commaSep lexer

reserved, reservedOp :: String -> Parser ()
reserved = T.reserved lexer
reservedOp = T.reservedOp lexer

symbol :: String -> Parser String
symbol = T.symbol lexer
braces :: Parser a -> Parser a
braces = T.braces lexer

parseOpTag = char '!' >> OpTag <$> identifier
parseConsName = ConsName <$> typeId

parens = T.parens lexer

parseExpr :: Parser Expr
parseExpr = try (parens parseExpr')
        <|> parseExpr'
  where
    parseExpr' = parseVar
             <|> parseLit
             <|> parseAbs
             <|> parseHandler
            --  <|> parseCons

    parseVar = Var <$> allID

    parseLit = fmap Lit $ parseInt <|> parseBool <|> parseUnit
      where
        parseInt = LInt . fromInteger <$> T.natural lexer
        parseBool = fmap LBool $
                      (reserved "True" >> return True)
                  <|> (reserved "False" >> return False)
        parseUnit = reservedOp "()" >> return LUnit

    parseAbs = symbol "\\" >>
      Abs <$> param <*> many identifier
        <*> (symbol "." >> parseComputation)

    parseHandler = reserved "handler" >> braces (do
      (x, c) <- option ("x", Ret (Var "x")) parsePureCase
      Handler x undefined c <$> parseOpCase)

    parsePureCase = do
      reserved "pure"
      x <- param
      reservedOp "->"
      c <- parseComputation
      reservedOp "|"
      return (x, c)
      
    parseOpCase = do
      res <- sepBy parseOp (reservedOp "|")
      return (foldr (\(op, x, k, c) l -> OpCase op x k c l)
                (Nil undefined) res)
      where
        parseOp = do
          op <- parseOpTag
          x <- param
          k <- param
          reservedOp "->"
          c <- parseComputation
          return (op, x, k, c)

    -- parseCons = Cons <$> parseConsName <*> many parseExpr


parseComputation :: Parser Computation
parseComputation = parens parseComputation'
               <|> parseComputation'
  where
    parseComputation' = parseRet
                    <|> try parseApp
                    <|> parseIf
                    <|> parseOpCall
                    <|> parseWithHandle
                    <|> parseAbsurd
                    <|> parseLet
                    <|> parseDo
                    <|> parseDoRec
                    <|> parseCase
                    <|> parseBinOp

    parseBinOp = parseBinOp' "+" Add
             <|> parseBinOp' "-" Sub
             <|> parseBinOp' "*" Mul
             <|> parseBinOp' "/" Div
             <|> parseBinOp' "==" Eq
             <|> parseBinOp' "<" Lt
             <|> parseBinOp' ">" Gt
             <|> parseBinOp' "&&" And
             <|> parseBinOp' "||" Or
      where
        parseBinOp' ch op = try $ do
          e1 <- parseExpr
          reservedOp ch
          binop' (genBinOP' op) e1 <$> parseExpr

    parseRet = reserved "pure" >> Ret <$> parseExpr

    parseApp = App <$> parseExpr <*> parseExpr <*> many parseExpr

    parseIf = do
      reserved "if"
      x <- parseExpr
      reserved "then"
      c1 <- parseComputation
      reserved "else"
      If x c1 <$> parseComputation

    parseOpCall = do
      op <- parseOpTag
      res <- parens (optionMaybe parseExpr)
      case res of
        Nothing -> return (OpCall op (Lit LUnit))
        Just e -> return (OpCall op e)

    parseWithHandle = do
      reserved "with"
      h <- parseExpr
      reserved "handle"
      WithHandle h <$> parseComputation

    parseAbsurd = reserved "absurd" >> Absurd undefined <$> parseExpr

    parseLet = do
      reserved "let"
      x <- identifier
      reservedOp "="
      e <- parseExpr
      Let x e <$> parseComputation

    parseDo = reserved "do" >> braces (do
        stmts' <- semiSep parseDoStmt
        let (stmts, ret) = (init stmts', last stmts')
        case ret of
          DoC c -> return (Do stmts c)
          _ -> parserFail "the last statement in do")
      where
          parseDoStmt = try parseBind <|> parseDoLet
                    <|> (DoC <$> parseComputation)

          parseBind = do
            x <- identifier
            reservedOp "<-"
            Bind x <$> parseComputation

          parseDoLet = do
            reserved "let"
            x <- identifier
            reservedOp "="
            DoLet x <$> parseExpr

    parseDoRec = do
      reserved "letrec"
      f <- identifier
      x <- identifier
      reservedOp "="
      c <- parseComputation
      reserved "in"
      DoRec f x c <$> parseComputation

    parseCase = do
      reserved "case"
      e <- parseExpr
      reserved "of"
      res <- braces (sepBy parseLine (reservedOp "|"))
      return (Case e res)
      where
        parseLine = do
          p <- parsePatternOuter
          reservedOp "->"
          c <- parseComputation
          return (p, c)

        parsePatternOuter = parseWild
                        <|> parsePVar
                        <|> parsePCons'
                        <|> parsePConsZero

        parsePatternInner = parseWild
                        <|> parsePVar
                        <|> parsePCons

        parseWild = reserved "_" >> return PWild
        parsePVar = PVar <$> identifier
        parsePCons = parens parsePCons'
                 <|> parsePConsZero
        parsePConsZero = do
          cons <- parseConsName
          return (PCons cons [])
        parsePCons' = do
          cons <- parseConsName
          ps <- many parsePatternInner
          return (PCons cons ps)

parseDecl :: Parser Decl
parseDecl = parseTermDecl
        <|> parseTermDeclRec
        <|> parseDataDecl
        <|> parseEffectDecl
  where
    parseTermDecl = do
      reserved "let"
      x <- identifier
      params <- many param
      reservedOp "="
      case params of
        [] -> TermDecl x <$> parseExpr
        (p:ps) -> parserTrace "t" >> (TermDecl x . Abs p ps <$> parseComputation)
          <* parserTrace "there"

    parseTermDeclRec = do
      reserved "letrec"
      f <- identifier
      x <- identifier
      reservedOp "="
      c <- parseComputation
      let res = TermDecl f (Abs x [] (DoRec f x c (App (Var f) (Var x) [])))
      return res

    parseDataDecl = do
      reserved "data"
      decls <- sepBy parseTypeTerm (reservedOp "|")
      reservedOp ":"
      x <- typeId
      return (DataDecl x decls)
      where
        parseTypeTerm = TypeTerm <$> parseConsName <*> many parsePureType

    parseEffectDecl = do
      reserved "effect"
      x <- typeId
      decls <- braces (sepBy parseOpDecl (reservedOp "|"))
      return (EffectDecl x decls)
      where
        parseOpDecl = do
          op <- parseOpTag
          reservedOp ":"
          t1 <- parsePureType
          reservedOp "=>"
          OpDecl op t1 <$> parsePureType

parsePureType :: Parser PureType
parsePureType = consCase <|> handCase
  where
    consCase = do
      cons <- TCon <$> typeId
      rest <- parsePureType'
      case rest of
        Nothing -> return cons
        Just f -> return (f cons)

    handCase = do
      hand <- parseTHandler
      rest <- parsePureType'
      case rest of
        Nothing -> return hand
        Just f -> return (f hand)

    parsePureType' = try (do
        reservedOp "->"
        d <- parseDirtyType
        rest <- parsePureType'
        case rest of
          Just f -> return $ Just (\e' -> f (e' `TFunc` d))
          Nothing -> return $ Just (`TFunc` d))
      <|> return Nothing

    parseTHandler = do
      t <- parseDirtyType
      reservedOp "=>"
      THandler t <$> parseDirtyType

parseDirtyType :: Parser DirtyType
parseDirtyType = braces $ do
  t <- parsePureType
  reservedOp "!"
  DirtyType t <$> parseDirt

parseDirt :: Parser Dirt
parseDirt = braces $ do
  x <- commaSep parseOpTag
  return (Dirt (Set.fromList x) undefined)

parseProgram :: Parser Program
parseProgram = do
  whiteSpace
  decls <- many parseDecl
  parserTrace "here"
  Program decls <$> optionMaybe parseMain
  where
    parseMain = do
      reserved "main"
      reservedOp "="
      parseComputation

test = parse parseComputation "dummy"
-- >>> test "do { x <- !read (1); pure 2 }"
-- Right do { x <- read(1); (return 2) }

parseHmr :: FilePath -> IO (Either ParseError Program)
parseHmr fileName = do
  code <- readFile fileName
  let res = parse parseProgram fileName code
  return res
