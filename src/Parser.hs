module Parser where

import Common
import Syntax
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
                , "absurd", "let", "do", "dorec", "case", "of"
                , "data", "effect", "main"]
reservedOpNames = ["+", "-", "*", "/", "==", "&&", "||"
                  , "->", "|", "=", ":"]
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

identifier :: Parser String
identifier = T.identifier lexer
-- semi = T.semi lexer
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
parseConsName = ConsName <$> identifier
parens = T.parens lexer

parseExpr :: Parser Expr
parseExpr = parseVar
        <|> parseLit
        <|> parseAbs
        <|> parseHandler
        <|> parseCons
  where
    parseVar = Var <$> identifier

    parseLit = fmap Lit $ parseInt <|> parseBool <|> parseUnit
      where
        parseInt = LInt . fromInteger <$> T.integer lexer
        parseBool = fmap LBool $
                      (reserved "True" >> return True)
                  <|> (reserved "False" >> return False)
        parseUnit = symbol "()" >> return LUnit

    parseAbs = symbol "\\" >>
      Abs <$> identifier <*> many identifier
          <*> (symbol "." >> parseComputation)

    parseHandler = do
      reserved "handler"
      x <- identifier
      c <- parseComputation
      Handler x undefined c <$> parseOpCase

    parseOpCase = do
      res <- braces (semiSep parseOp)
      return (foldr (\(op, x, k, c) l -> OpCase op x k c l)
                (Nil undefined) res)
      where
        parseOp = do
          op <- parseOpTag
          x <- identifier
          k <- identifier
          reservedOp "->"
          c <- parseComputation
          return (op, x, k, c)

    parseCons = Cons <$> parseConsName <*> many parseExpr


parseComputation :: Parser Computation
parseComputation = parseRet
               <|> parseApp
               <|> parseIf
               <|> parseOpCall
               <|> parseWithHandle
               <|> parseAbsurd
               <|> parseLet
               <|> parseDo
               <|> parseDoRec
               <|> parseCase
  where
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
      h <- braces parseExpr
      reserved "handle"
      c <- braces parseComputation
      return (WithHandle h c)

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
          parseDoStmt = parseBind <|> parseDoLet
                    <|> (DoC <$> parseComputation)

          parseBind = do
            x <- identifier
            reservedOp "<-"
            Bind x <$> parseComputation

          parseDoLet = do
            x <- identifier
            reservedOp "="
            DoLet x <$> parseExpr

    parseDoRec = do
      reserved "dorec"
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
      res <- braces (semiSep parseLine)
      return (Case e res)
      where
        parseLine = do
          p <- parsePattern
          reservedOp "->"
          c <- parseComputation
          return (p, c)

        parsePattern = (reserved "_" >> return PWild)
                   <|> PVar <$> identifier
                   <|> (PCons <$> parseConsName <*> many parsePattern)

parseDecl :: Parser Decl
parseDecl = parseTermDecl
        <|> parseDataDecl
        <|> parseEffectDecl
  where
    parseTermDecl = do
      reserved "let"
      x <- identifier
      reservedOp "="
      TermDecl x <$> parseExpr

    parseDataDecl = do
      reserved "data"
      decls <- sepBy parseTypeTerm (reservedOp "|")
      reservedOp ":"
      x <- identifier
      return (DataDecl x decls)
      where
        parseTypeTerm = TypeTerm <$> parseConsName <*> many parsePureType

    parseEffectDecl = do
      reserved "effect"
      x <- identifier
      decls <- braces (semiSep parseOpDecl)
      return (EffectDecl x decls)
      where
        parseOpDecl = do
          op <- parseOpTag
          reservedOp ":"
          t1 <- parsePureType
          reservedOp "->"
          OpDecl op t1 <$> parsePureType

parsePureType :: Parser PureType
parsePureType = consCase <|> handCase
  where
    consCase = do
      cons <- TCon <$> identifier
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
  reserved "main"
  reservedOp "="
  Program decls <$> parseComputation

test = parse parseComputation "dummy"
-- >>> test "do { x <- !read (1); pure 2 }"
-- Right do { x <- read(1); (return 2) }

parseHmr :: FilePath -> IO (Either ParseError Program)
parseHmr fileName = do
  code <- readFile fileName
  let res = parse parseProgram fileName code
  return res
