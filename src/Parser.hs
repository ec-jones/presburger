module Parser (parseFormula) where

import Formula
  ( Formula (And, Equals, Exists, Forall, Not, Or),
    Term (..),
  )
import Text.ParserCombinators.Parsec (Parser, parse, (<|>))
import Text.ParserCombinators.Parsec.Expr
  ( Assoc (AssocLeft),
    Operator (Infix, Prefix),
    buildExpressionParser,
  )
import Text.ParserCombinators.Parsec.Language
  ( GenLanguageDef (reservedNames, reservedOpNames),
    LanguageDef,
    emptyDef,
  )
import qualified Text.ParserCombinators.Parsec.Token as Token

parseFormula :: String -> Formula String
parseFormula s =
  case parse formula "" s of
    Left e -> error (show e)
    Right r -> r

formulaDef :: LanguageDef a
formulaDef =
  emptyDef
    { reservedOpNames = ["+", "¬", "/\\", "\\/", "=", "."],
      reservedNames = ["forall", "exists"]
    }

lexer :: Token.TokenParser a
lexer = Token.makeTokenParser formulaDef

identifier :: Parser String
identifier = Token.identifier lexer

reserved, reservedOp :: String -> Parser ()
reserved = Token.reserved lexer
reservedOp = Token.reservedOp lexer

parens :: Parser a -> Parser a
parens = Token.parens lexer

integer :: Parser Integer
integer = Token.integer lexer

term :: Parser (Term String)
term = buildExpressionParser [[Infix (reservedOp "+" >> return Add) AssocLeft]] innerTerm
  where
    innerTerm =
      parens term
        <|> fmap Var identifier
        <|> ( do
                i <- integer
                case i of
                  0 -> return Zero
                  1 -> return One
                  _ -> fail ""
            )

formula :: Parser (Formula String)
formula =
  buildExpressionParser
    [ [Prefix (reservedOp "¬" >> return Not)],
      [Infix (reservedOp "/\\" >> return And) AssocLeft],
      [Infix (reservedOp "\\/" >> return Or) AssocLeft],
      [Prefix exists, Prefix forall]
    ]
    innerFormula
  where
    exists = do
      reserved "exists"
      x <- identifier
      reservedOp "."
      return (Exists x)
    forall = do
      reserved "forall"
      x <- identifier
      reservedOp "."
      return (Forall x)
    innerFormula =
      parens formula
        <|> (forall <*> formula)
        <|> (exists <*> formula)
        <|> ( do
                t1 <- term
                reservedOp "="
                Equals t1 <$> term
            )