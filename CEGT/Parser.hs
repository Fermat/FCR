{-#LANGUAGE PackageImports, StandaloneDeriving, DeriveDataTypeable, FlexibleContexts#-}
module Parser where
import Syntax

import Text.Parsec hiding (ParseError,Empty, State)
import qualified Text.Parsec as P
import Text.Parsec.Language
import Text.Parsec.Char
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import qualified Text.Parsec.Token as Token

import Control.Applicative hiding ((<|>),many, optional)
import Control.Monad.State.Lazy
import "mtl" Control.Monad.Identity
import Control.Exception(Exception)

import qualified Data.IntMap as IM
import Data.Typeable
import Data.Char
import Data.List

parseModule :: String -> String -> Either P.ParseError Module
parseModule srcName cnts =
  runIdentity $ runParserT gModule () srcName cnts

type Parser a = Parsec String () a

deriving instance Typeable P.ParseError
instance Exception P.ParseError 

-- parse module
gModule :: Parser Module
gModule = do
  bs <- many gDecl
  eof
  return $ Module bs

gDecl :: Parser Decl
gDecl = ruleDecl

ruleDecl :: Parser Decl
ruleDecl = do
  c <- con 
  reservedOp ":"
  t <- rule
  return $ Rule c t
  
var :: Parser Exp
var = do
  n <- identifier
  when (isUpper (head n)) $ parserZero
  return (Var n)

ensureLower :: Parser String
ensureLower = do
  n <- identifier
  when (isUpper (head n)) $ unexpected "expected to begin with lowercase letter"
  return n

ensureUpper :: Parser String
ensureUpper = do
  n <- identifier
  when (isLower (head n)) $ unexpected "expected to begin with uppercase letter"
  return n

con :: Parser Exp
con = do
  n <- identifier
  when (isLower (head n)) $ parserZero
  return (Constr n)

-- parser for FType--
rule :: Parser Exp
rule = do
  t1 <- term
  reserved "~>"
  t2 <- term
  return $ Arrow t1 t2
  
term :: Parser Exp
term = compound 

compound = do
  n <- try var <|> con
  as <- compoundArgs
  if null as then return n
    else return $ foldl' (\ z x -> App z x) n as 

compoundArgs = 
  many (try con <|> try var <|> try (parens term))


-----------------------Positions -------
  
wrapPos :: Parser Exp -> Parser Exp
wrapPos p = pos <$> getPosition <*> p
  where pos x (Pos y e) | x==y = (Pos y e)
        pos x y = Pos x y


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

tokenizer :: Token.GenTokenParser String u Identity
tokenizer = Token.makeTokenParser gottlobStyle

identifier :: ParsecT String u Identity String
identifier = Token.identifier tokenizer

whiteSpace :: ParsecT String u Identity ()
whiteSpace = Token.whiteSpace tokenizer

reserved :: String -> ParsecT String u Identity ()
reserved = Token.reserved tokenizer

reservedOp :: String -> ParsecT String u Identity ()
reservedOp = Token.reservedOp tokenizer

operator :: ParsecT String u Identity String
operator = Token.operator tokenizer

colon :: ParsecT String u Identity String
colon = Token.colon tokenizer

integer :: ParsecT String u Identity Integer
integer = Token.integer tokenizer

brackets :: ParsecT String u Identity a -> ParsecT String u Identity a
brackets = Token.brackets tokenizer

parens :: ParsecT String u Identity a -> ParsecT String u Identity a
parens  = Token.parens tokenizer

braces :: ParsecT String u Identity a -> ParsecT String u Identity a
braces = Token.braces tokenizer

dot :: ParsecT String u Identity String
dot = Token.dot tokenizer

commaSep1 :: ParsecT String u Identity a -> ParsecT String u Identity [a]
commaSep1 = Token.commaSep1 tokenizer

semiSep1 :: ParsecT String u Identity a -> ParsecT String u Identity [a]
semiSep1 = Token.semiSep1 tokenizer

comma :: ParsecT String u Identity String
comma = Token.comma tokenizer

