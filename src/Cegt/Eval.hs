module Cegt.Eval where
import Cegt.Syntax
import Cegt.Monad
import Cegt.PrettyPrinting
import Cegt.Rewrite

import Data.List
import Data.Char

import Control.Monad.State
import Text.PrettyPrint

eval :: Env -> Int -> Exp -> Exp
eval env n e = undefined

unfold :: Env -> Exp -> Exp
unfold env (Var x) = let lms = lemmas env in
  case lookup x lms of
    Nothing -> error $ "undefined var" ++ show x
    Just (pf, f) -> pf
                         
unfold env (Const x) = Const x

unfold env (App (Lambda x _ t) e2) =
  let a = runSubst e2 x t
      b = normEvidence a
  in unfold env b
     
unfold env (App (Const k) e2) =
  App (Const k) $ unfold env e2

unfold env (App e1 e2) =
  let a = unfold env e1 in unfold env (App a e2)

unfold env (TApp e1 t1) = 
  
      
  
