module Parser where
import Text.Parsec hiding (ParseError,Empty, State)
import qualified Text.Parsec as P
import Text.Parsec.Language
import Text.Parsec.Char
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import qualified Text.Parsec.Token as Token
import Text.Parsec.Indent

import Control.Applicative hiding ((<|>),many, optional)
import Control.Monad.State.Lazy
import Control.Exception(Exception)

import qualified Data.IntMap as IM
import Data.Typeable
import Data.Char
import Data.List

parseTRS :: String -> String -> Either P.ParseError Module
parseModule srcName cnts =
  runIndent srcName $
  runParserT gModule initialParserState srcName cnts

