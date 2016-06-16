module Cegt.Guardness where
import Cegt.Syntax
import Cegt.Monad
import Cegt.PrettyPrinting

import Data.List
import Data.Char

import Control.Monad.State
import Text.PrettyPrint

alg :: [Name] -> Exp -> Bool
alg vs (Const _) = True
alg vs (Var x) | x `elem` vs = True
alg vs a@(Lambda x _ t) =
  let b = viewLBody a
      freshvars = map fst $ viewLVars a
      b' = flatten b
  in and $ map (alg (freshvars ++ vs)) b'

alg vs a@(App t' t) =
  let b' = flatten a
  in and $ map (alg vs) b'

