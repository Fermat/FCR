{-#LANGUAGE PackageImports, StandaloneDeriving, DeriveDataTypeable, FlexibleContexts#-}
module Cegt.Parser where
import Cegt.Syntax

import Text.Parsec hiding (ParseError,Empty, State)
import qualified Text.Parsec as P
import Text.Parsec.Language
import Text.Parsec.Char
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import qualified Text.Parsec.Token as Token
import Text.Parsec.Indent
import Control.Applicative hiding ((<|>),many, optional, Const)
import Control.Monad.State.Lazy
import "mtl" Control.Monad.Identity
import Control.Exception(Exception)

import qualified Data.IntMap as IM
import Data.Typeable
import Data.Char
import Data.List

parseModule :: String -> String -> Either P.ParseError Module
parseModule srcName cnts =
  runIndent srcName $ runParserT gModule () srcName cnts

parseExp :: String -> Either P.ParseError Exp
parseExp s = runIndent [] $ runParserT (try (parens term) <|> term) () [] s

-- parseExps :: String -> Either P.ParseError [Exp]
-- parseExps s = runIndent [] $ runParserT (many1 (try (parens term) <|> term)) () [] s

type Parser a = IndentParser String () a

-- deriving instance Typeable P.ParseError
-- instance Exception P.ParseError 

-- parse module
gModule :: Parser Module
gModule = do
  bs <- many ruleDecl
  eof
  return $ bs

ruleDecl :: Parser (Name, Exp)
ruleDecl = do
  (Const c) <- con 
  reservedOp ":"
  t <- rule
  return $ (c, t)
  
var :: Parser Exp
var = do
  n <- identifier
  when (isUpper (head n)) $ parserFail "expected to begin with lowercase letter"
  return (Var n)

con :: Parser Exp
con = do
  n <- identifier
  when (isLower (head n)) $ parserFail "expected to begin with uppercase letter"
  return (Const n)

-- parser for FType--
rule :: Parser Exp
rule = do
  t1 <- term
  reserved "~>"
  t2 <- term
  return $ Arrow t1 t2
  
term :: Parser Exp
term = lambda <|> compound 

lambda = do
  reservedOp "\\"
  as <- many1 var
  reservedOp "."
  p <- term
  return $ foldr (\ x y -> Lambda x y) p (map (\(Var x) -> x) as)
  
compound = do
  n <- try var <|> con
  as <- compoundArgs
  if null as then return n
    else return $ foldl' (\ z x -> App z x) n as 

compoundArgs =
  many $ indented >> (try con <|> try var <|> try (parens term))


-----------------------Positions -------
  
-- wrapPos :: Parser Exp -> Parser Exp
-- wrapPos p = pos <$> getPosition <*> p
--   where pos x (Pos y e) | x==y = (Pos y e)
--         pos x y = Pos x y


-------------------------------

-- Tokenizer definition

gottlobStyle :: (Stream s m Char, Monad m) => Token.GenLanguageDef s u m
gottlobStyle = Token.LanguageDef
                { Token.commentStart   = "{-"
                , Token.commentEnd     = "-}"
                , Token.commentLine    = "--"
                , Token.nestedComments = True
                , Token.identStart     = letter
                , Token.identLetter    = alphaNum <|> oneOf "_'"
                , Token.opStart        = oneOf ":!#$%&*+.,/<=>?@\\^|-"
                , Token.opLetter       = (oneOf ":!#$%&*+.,/<=>?@\\^|-") <|> alphaNum
                , Token.caseSensitive  = True
                , Token.reservedNames =
                  [
                    "forall", "iota", "reduce", 
                    "cmp","invcmp", "inst", "mp", "discharge", "ug", "beta", "invbeta",
                    "by", "from", "in", "let", "simpCmp", "invSimp",
                    "case", "of",
                    "data", "if", "then", "else",
                    "axiom", "proof", "qed", "lemma", "auto",
                    "show",
                    "where", "module",
                    "infix", "infixl", "infixr", "pre", "post",
                    "formula", "prog", "set",
                    "tactic", "deriving", "Ind"
                  ]
               , Token.reservedOpNames =
                    ["\\", "->", "|", ".","=", "::", ":", "=>"]
                }

tokenizer :: Token.GenTokenParser String u (State SourcePos)
tokenizer = Token.makeTokenParser gottlobStyle

identifier :: ParsecT String u (State SourcePos) String
identifier = Token.identifier tokenizer

whiteSpace :: ParsecT String u (State SourcePos) ()
whiteSpace = Token.whiteSpace tokenizer

reserved :: String -> ParsecT String u (State SourcePos) ()
reserved = Token.reserved tokenizer

reservedOp :: String -> ParsecT String u (State SourcePos) ()
reservedOp = Token.reservedOp tokenizer

operator :: ParsecT String u (State SourcePos) String
operator = Token.operator tokenizer

colon :: ParsecT String u (State SourcePos) String
colon = Token.colon tokenizer

integer :: ParsecT String u (State SourcePos) Integer
integer = Token.integer tokenizer

brackets :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) a
brackets = Token.brackets tokenizer

parens :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) a
parens  = Token.parens tokenizer

braces :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) a
braces = Token.braces tokenizer

dot :: ParsecT String u (State SourcePos) String
dot = Token.dot tokenizer

commaSep1 :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) [a]
commaSep1 = Token.commaSep1 tokenizer

semiSep1 :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) [a]
semiSep1 = Token.semiSep1 tokenizer

comma :: ParsecT String u (State SourcePos) String
comma = Token.comma tokenizer

