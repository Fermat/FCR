module Fcr.Typeinfer where

import Fcr.Syntax
import Fcr.Monad
import Fcr.Rewrite hiding (merge')
import Fcr.PrettyPrinting
import Fcr.Typecheck

import Control.Monad.State
import Text.PrettyPrint
import Data.List
import Data.Char
import Debug.Trace
import qualified Data.Set as S
-- [(Var|Const : Types)]
type PfEnv = [(Name, Exp)]

-- (global name for the proof, Mixed proof and goals,
--    [(position, current goal, current program, Environment, Scope list)],
--      Error message, counter for generating new variable during the resolution)
type ResState = (Name, Exp, [(Pos, Exp, Exp, PfEnv, LVars)], Maybe Doc, Int)

transit :: ResState -> ResState
transit (gn, pf, (pos, goal@(Imply x y), exp@(Lambda x Nothing t), gamma, lvars):phi, m, i) =
  let (bs, h) = getPre goal
      (vars, b) = (map fst $ viewLVars exp, viewLBody exp) in
    if length bs == length vars then
      let newEnv = zip vars bs
          newLam = foldr (\ (a, e) b -> Lambda a (Just e) b) h newEnv
          pf' = replace pf pos newLam
          pos' = pos ++ take (length bs) stream2
      in (gn, pf', (pos', h, t, gamma++newEnv, lvars):phi, Nothing, i)
    else  let m' = Just $
                   text "arity mismatch when performing lambda abstraction" $$
                   (nest 2 (text "current goal: " <+>text goal)) $$ nest 2
                   (text "current program:"<+> disp exp) $$
                   (nest 2 $ text "current mixed proof term" $$ nest 2 (disp pf))
          in [(gn, pf, (pos, goal, exp, gamma, lvars):phi, m', i)]

      
transit (gn, pf, (pos, goal@(Forall x y), exp, gamma, lvars):phi, m, i) =
  let (vars, imp) = getVars goal
      lv = length vars
      absNames = zipWith (\ x y -> x ++ show y ++ "'") vars [i..]
      sub = zip vars (map Const absNames)
      imp' = applyE sub imp
      newAbs = foldr (\ a b -> Lambda a Nothing b) imp' absNames
      pf' = replace pf pos newAbs
      pos' = pos ++ take lv stream2
  in (gn, pf', (pos',imp', gamma, lvars++ absNames):phi, Nothing, i+lv)

transit (gn, pf, (pos, goal, exp@(App p1 p2), gamma, lvars):phi, m, i) =
  let x:xs = flatten exp
