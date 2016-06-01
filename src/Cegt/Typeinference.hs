module Cegt.Typeinference where

import Cegt.Syntax
import Cegt.Interaction
import Cegt.Monad
import Cegt.Rewrite hiding (merge')

import Cegt.PrettyPrinting
import Cegt.Typecheck
import Control.Monad.State
import Text.PrettyPrint
import Data.List
import Data.Char
import Debug.Trace
{-
env2 = [("H", KArrow Star (KArrow Star Star)), ("J", KArrow Star Star), ("G", KArrow Star Star), ("S", KArrow Star Star)]
exp1 = (Lambda "a1" Nothing
        (Lambda "a2" Nothing
         (Lambda "a3" Nothing
          (App (Var "a3")
           (App (Var "a1")
            (App (Var "a2")
             (App (App (App (Var "h")
                        (Lambda "b1" Nothing (App (Var "a1") (App (Var "a2") (Var "b1")))))
                   (Var "a2"))
              (Var "a3"))))))))

f1 = Forall "p'" (Forall "f" (Forall "x" (Forall "z" (Imply (Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (PApp (Var "f") (PApp (Const "S") (Var "x"))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "z"))))) (PApp (Var "p") (PApp (PApp (Var "f") (Var "x")) (Var "y"))))))) (Imply (Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (PApp (Const "H") (Var "x")) (PApp (Const "S") (Var "y")))) (PApp (Var "p") (PApp (PApp (Const "H") (PApp (Const "S") (Var "x"))) (Var "y"))))))) (Imply (Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (Const "J") (Var "y"))) (PApp (Var "p") (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "y")))))))) (PApp (Var "p'") (PApp (PApp (Var "f") (PApp (Const "S") (Var "x"))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "z")))))))))))

g2 = PApp (Var "p'") (PApp (PApp (Var "f") (PApp (Const "S") (PApp (Const "S") (Var "x")))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (PApp (Const "S") (Var "z")))))

h2 = PApp (Var "p1fresh") (PApp (PApp (Const "H") (PApp (Const "S") (Var "x2fresh"))) (Var "y3fresh"))
initstate1 = [("h", f1, [([], f1, [("h", f1)])])]
man1 = construction "h" env2 initstate1 exp1 -- [s | s <- construction "h" env2 initstate1 exp1, success s]
man3 = construction "h" env2 initstate1 (Var "h")

g1 = PApp (Var "p'") (PApp (PApp (Var "f") (PApp (Const "S") (PApp (Const "S") (Var "x")))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (PApp (Const "S") (Var "z")))))

h1 = PApp (Var "p'1") (PApp (PApp (Var "f2") (PApp (Const "S") (Var "x3"))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x3")) (Var "z4"))))
man2 = runHMatch env2 h1 g1 
success :: ProofState -> Bool
success (gn,pf,[]) = True
success _ = False

construction :: Name -> KSubst -> [ProofState] -> Exp -> [ProofState]
construction n ks init exp | trace (show ( n) ++ "-- " ++show (disp exp)) False = undefined
construction n ks init (Var v) =
  [s | Just s <- map (\ x -> useF x v) init]

construction n ks init a@(Lambda x Nothing t) =
  let (vars, b) = (map fst $ viewLVars a, viewLBody a)
      new = map (\ x -> intros x vars) init 
  in construction n ks new b

construction n ks init (App (Const k) p2) =
  let next = [s | Just s <- map (\ x -> applyF x k) init]
  in
   if null next then
     do nex <-  map (\x -> applyH ks x k) init
        construction n ks nex p2
   else construction n ks next p2


construction n ks init (App (Var v) p2) | v /= n =
  let next = [s | Just s <- map (\ x -> applyF x v) init]
  in
   if null next then
     do nex <-  map (\x -> applyH ks x v) init
        construction n ks nex p2
   else construction n ks next p2

-- Has bug
construction n ks init (App (Var v) p2) | v == n =
  do next <-  map (\x -> applyH ks x v) init
     
     construction n ks next p2
--  x App (App y z) q
construction n ks init a@(App p1 p2) = 
  case flatten a of
    (Var v): xs | v == n ->
      do next <- map (\ x -> applyH ks x v) init 
         foldr (\ z x -> construction n ks x z) next xs


-- construction n ks init a@(App p1 p2) =
-}
      

-- Second order matching, using Gilles Dowek's terminology in his tutorial.
-- tips: the less number of higher order variable, the less number of
-- possible substitution we get. 

kenv = [("Z", Star), ("S", KArrow Star Star), ("T", Star), ("d", KArrow Star (KArrow Star Star))]
t1 = PApp (Var "p") (PApp (PApp (Const "d") (Const "Z")) (Const "Z"))
t1' = PApp (Var "p1") (PApp (PApp (Const "d") (Const "Z")) (Const "Z"))
t2 = (PApp (PApp (Var "d1") (Const "Z")) (PApp (Const "S") (Const "Z")))
t3 = PApp (Const "B") (PApp (Var "l") (PApp (Const "B") (Var "x")))
t4 = PApp (Const "B") (PApp (Var "l1") (PApp (Const "A") (PApp (Const "B") (Var "y"))))
t5 = PApp (PApp (PApp (PApp (Var "g") (Const "T")) (Const "T")) (Const "Z")) (PApp (Var "s") (Const "Z"))
t6 = PApp (PApp (PApp (PApp (Var "g1") (Const "T")) (Const "T")) (PApp (Const "S") (Const "Z")))
     (PApp (Var "s1") (PApp (Var "s1") (Const "Z")))
-- hmatch :: MonadPlus m => KSubst -> Exp -> Exp -> StateT Int m [Subst]
-- test1 :: [[Subst]]


a1 = evalState (hmatch kenv t1' t1) 0
a2 = wellKind (free t1') kenv a1
a3 = runHMatch [("B", KArrow Star Star), ("A", Star)] (PApp (Const "B") (Var "q")) (PApp (Const "B") (Const "A"))
a4 = runHMatch [("A", KArrow Star Star), ("B", KArrow Star Star)] t3 t4
a5 = runHMatch kenv t5 t6
test1 = sep $ map (\ x -> text "[" <+> disp x <+> text "]") $ a2
test2 = length a1
test3 = sep $ map (\ x -> text "[" <+> disp x <+> text "]") $ a4
test4 = length a2
-- test5 = sep $ map (\ x -> text "[" <+> disp x <+> text "]") $ man2
