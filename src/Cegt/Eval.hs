module Cegt.Eval where
import Cegt.Syntax
import Cegt.Monad
import Cegt.PrettyPrinting
import Cegt.Rewrite

import Data.List
import Data.Char

import Control.Monad.State
import Text.PrettyPrint
import Debug.Trace

eval :: Env -> Int -> Exp -> Either Doc Exp
eval env n e | n == 0 = Left (text "wrong")
eval env n e =
  let res = unfold env e
      as = axioms env 
  in case res of
    g@(App e1 e2) -> case flatten e1 of
                     (Const k) : cxt : xs -> if n == 1 then
                                               let (Just f) = lookup k as
                                                   fhead = last (flattenF (viewFBody f))
                                                   vars = viewFVars f
                                                   subs = zip vars (cxt:xs)
                                                   f'' = normalize $ applyE subs fhead
                                               in Right f''
                                             else eval env (n-1) e2
                     a -> eval env n g
                       -- Left $ text "unknown error from eval1" <+> text (show a)
    g -> eval env n g -- Left $ text "unknown error from eval2"

-- K P Ins1 .. (K2 ... ())       
-- unfold' env t = let t1 = unfold env t
--                     t2 = unfold env t1
--                 in if t1 == t2 then t1 else unfold' env t2

-- one step par unfold
unfold :: Env -> Exp -> Exp
-- unfold ks exp | trace ("-- " ++show (disp exp)) False = undefined
unfold env (Var x) = let lms = lemmas env in
  case lookup x lms of
    Nothing -> error $ "undefined var" ++ show x
    Just (pf, f) -> pf
                         
unfold env (Const x) = Const x

unfold env (App (Lambda x (Just _) t) e2) =
  let a = runSubst e2 (Var x) t
      b = normEvidence a
  in b
     
unfold env (App (Const k) e2) =
  App (Const k) $ unfold env e2

unfold env (App e1 e2) =
  let a = unfold env e1
      b = unfold env e2
  in case App a b of
          c@(App (Lambda x _ t) t') -> unfold env c
          d -> d

unfold env (TApp (Lambda x Nothing t) t1) =
  let a = runSubst t1 (Var x) t
      b = normEvidence a
  in b

unfold env a@(TApp (Const k) e2) = a
unfold env (TApp e1 e2) =
  let a = unfold env e1 in (TApp a e2)
  
unfold env a@(Lambda x t1 t2) = a



  
