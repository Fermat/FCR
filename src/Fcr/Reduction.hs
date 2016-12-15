module Fcr.Reduction where

import Fcr.Syntax
import Fcr.Monad
import Fcr.Rewrite hiding (merge', reduce)
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
-- [(position, current sub goal, Environment)],
-- Error message, counter for generating new variable during the resolution)
type ProofState = (KSubst, Name, Exp, [(Pos, Exp, PfEnv, Exp)], Maybe Doc, Int)

reduce :: [ProofState] -> [ProofState]
reduce ((ks, gn, pf, [], Nothing, i):tai) = reduce tai
reduce ((ks, gn, pf, res, Just m, i):tai) = (ks, gn, pf, res, Just m, i) : reduce tai
reduce ((ks, gn, pf, (pos, goal, gamma, a@(Lambda x Nothing t)):res, Nothing, i):tai) =
  let (ns, b) = (map fst $ viewLVars a, viewLBody a)
      (vars, head, body) = separate goal
      lb = length body
      lv = length vars
      num = lv + lb
      impNames = ns 
      absNames = zipWith (\ x y -> x ++ show y ++ "'") vars [i..]
      sub = zip vars (map Const absNames)
      body' = map (\ x -> applyE sub x) body
      head' = applyE sub head
      newEnv = zip impNames body'
      newLam = foldr (\ (a, exp) b -> Lambda a (Just exp) b) head' newEnv
      newAbs = foldr (\ a b -> Lambda a Nothing b) newLam absNames
      pf' = replace pf pos newAbs
      pos' = pos ++ take num stream2
  in reduce $ (ks, gn, pf', (pos',head', gamma++newEnv, b):res, Nothing, i+lv):tai

reduce ((ks, gn, pf, curState@((pos, goal, gamma, App p1 p2):res), Nothing, i):tai) =
  let (k':es) = flatten (App p1 p2)
      k = extract k'
  in
    case lookup k gamma of
      Nothing -> let m' = Just $ text "can't find" <+> text k <+> text "in the environment" in
        (ks, gn, pf, (pos, goal, gamma, App p1 p2):res, m', i) : reduce tai
      Just f ->
        let (vars, head, body) = separate f
            i' = i + length vars
            fresh = map (\ (v, j) -> v ++ show j ++ "'") $ zip vars [i..]
            renaming = zip vars (map Var fresh)
            body'' = map (applyE renaming) body
            head'' = applyE renaming head
            ss = runHMatch ks head'' goal
          -- trace (show head''++ "--from rhm--"++ show goal ++ show k) $
        in case ss of
             [] ->
               let m' = Just $
                        text "can't match" <+> disp (head'') $$ text "against"
                        <+> disp (goal) $$
                        (nest 2 (text "when applying" <+>text k <+> text ":" <+> disp f)) $$
                        (nest 2 $ text "current mixed proof term" $$ nest 2 (disp pf))
               in (ks, gn, pf, (pos, goal, gamma, App p1 p2):res, m', i) : reduce tai
             _ -> 
                 let newState = [(ks, gn, pf', new++res, Nothing, i') |
                                  sub <- ss,
                                  let body' = map normalize $ (map (applyE sub) body''),
                                  let head' = normalize $ applyE sub head'',
                                  let np = ([ s | r <- fresh, let s = case lookup r sub of
                                                                        Nothing -> (Var r)
                                                                        Just t -> t]),
                                  let contm = foldl' (\ z x -> App z x)
                                                     (foldl' (\ z x -> TApp z x) k' np) body',
                                  let pf' = replace pf pos contm,
                                  let zeros = makeZeros $ length body',
                                  let ps = map (\ x -> pos++x++[1]) zeros,
                                  let reArrange = arrange $ zip (zip ps body') es,
                                  let new = map (\((p, g), l') -> (p, g, gamma,l')) reArrange] in
                          reduce $ newState++tai                              
                    

reduce ((ks, gn, pf, curState@((pos, goal, gamma, Const k):res), Nothing, i):tai) =
  case lookup k gamma of
    Nothing -> let m' = Just $ text "can't find" <+> text k <+> text "in the environment" in
      (ks, gn, pf, (pos, goal, gamma, Const k):res, m', i) : reduce tai
    Just f ->
      if f `alphaEq` goal then
        let name = Const k
            pf' = replace pf pos name
        in  reduce $ (ks, gn, pf', res, Nothing, i):tai
      else 
        let m' = Just $
                 text "can't match" <+> disp f $$ text "against"
                 <+> disp (goal) $$
                 (nest 2 (text "when applying" <+>text k <+> text ":" <+> disp f)) $$
                 (nest 2 $ text "current mixed proof term" $$ nest 2 (disp pf))
        in (ks, gn, pf, (pos, goal, gamma, Const k):res, m', i) : reduce tai

reduce ((ks, gn, pf, curState@((pos, goal, gamma, Var k):res), Nothing, i):tai) =  
  case lookup k gamma of
    Nothing -> let m' = Just $ text "can't find" <+> text k <+> text "in the environment" in
      (ks, gn, pf, (pos, goal, gamma, Const k):res, m', i) : reduce tai
    Just f ->
      if f `alphaEq` goal then
        let name = Const k
            pf' = replace pf pos name
        in  reduce $ (ks, gn, pf', res, Nothing, i):tai
      else 
        let (vars, head, body) = separate f
            i' = i + length vars
            fresh = map (\ (v, j) -> v ++ show j ++ "'") $ zip vars [i..]
            renaming = zip vars (map Var fresh)
            body'' = map (applyE renaming) body
            head'' = applyE renaming head
            ss = runHMatch ks head'' goal
        in case ss of
             [] ->
               let m' = Just $
                        text "can't match" <+> disp (head'') $$ text "against"
                        <+> disp (goal) $$
                        (nest 2 (text "when applying" <+>text k <+> text ":" <+> disp f)) $$
                        (nest 2 $ text "current mixed proof term" $$ nest 2 (disp pf))
               in (ks, gn, pf, (pos, goal, gamma, Var k):res, m', i) : reduce tai
             _ -> 
               let newStates = [ (ks, gn, pf', res', Nothing, i) | sub <- ss,
                                      let evars = free head'',
                                      let refresher = [(x, t) | x <- evars,
                                                       (y, t) <- sub, x == y],
                                      let pf1 = normEvidence $ applyE refresher pf,
                                      let res' = map (\ (a, gl, gm, e') ->
                                                         (a, normalize $ applyE refresher gl, (map (\ (x, y) -> (x, normalize $ applyE refresher y)) gm), e')) res,
                                      let head' = normalize $ applyE sub head'',
                                      let name = Var k,
                                      let pf' = replace pf1 pos name,
                                      scopeCheck refresher pf ] in
                            reduce $ newStates ++ tai
               




  
arrange :: [((Pos, Exp), Exp)] -> [((Pos, Exp), Exp)]
arrange ls = let low = [ ((p, f), e) | ((p, f), e) <- ls, let fr = free f, not (null fr), 
                         let (vars, h, _) = separate f, not $ null (fr `intersect` (free h))]
                 high = filter (\ l -> not (l `elem` low)) ls
             in high ++ low



scopeCheck :: [(Name, Exp)] -> Exp -> Bool
scopeCheck sub pf =
  let codom = map rebind (map snd sub)
      vars = concat $ map free codom
      epos = concat [getPos v pf | v <- map fst sub ]
      varpos = concat [map init (getPos' v pf) | v <- vars ]
  in and [ v `isPrefixOf` e | e <- epos, v <- varpos ]                   
                    
getPos :: Name -> Exp -> [Pos]
getPos x (Var y) = if x == y then [[]] else []
getPos x (Const y) = []
getPos x (App t1 t2) = (map (0:) $ getPos x t1) ++ (map (1:) $ getPos x t2)
getPos x (TApp t1 t2) = (map (0:) $ getPos x t1) ++ (map (1:) $ getPos x t2)
--map (0:) $ getPos x t1
getPos x (Lambda n _ t2) = map (1:) $ getPos x t2
getPos x _ = []

extract (Const v) = v
extract (Var v) = v
-- get position of lambda bind var
getPos' :: Name -> Exp -> [Pos]
getPos' x (Var y) = []
getPos' x (Const y) = []
getPos' x (App t1 t2) = (map (0:) $ getPos' x t1) ++ (map (1:) $ getPos' x t2)
getPos' x (TApp t1 t2) = (map (0:) $ getPos' x t1) 
--map (0:) $ getPos' x t1
getPos' x (Lambda n _ t2) = if x == n then [[0]] else map (1:) $ getPos' x t2
getPos' x _ = []

  

separate f = let (vars, imp) = getVars f
                 (bs, h) = getPre imp
             in (vars, h, bs)

getPre ::  Exp -> ([Exp],Exp)
getPre (Imply x y) = let (bs, t') = getPre y in (x:bs, t')
getPre t = ([], t)

getVars :: Exp -> ([Name],Exp)
getVars (Forall x t) = let (xs, t') = getVars t in (x:xs, t')
getVars t = ([], t)

-- makeZeros n | trace ("myZeros " ++ show n) False = undefined
makeZeros 0 = []
makeZeros n | n > 0 = make n : makeZeros (n-1)

stream = 0:stream
stream2 = 2:stream2
make n | n > 0 = take (n-1) stream

constrProof :: Name -> [ProofState] -> KSubst -> Exp -> Either Doc Exp
constrProof n ini ks exp =
  let finals = construction' n ks ini exp in
  case [s | s <- finals, success s] of
        (_, pf, _, _, _):_ -> Right pf -- trace (show $ disp pf) $ 
        [] -> let rs = map (\ a -> case a of
                               (_, _, (_,g,_):_ , m, _) ->
                                 case m of
                                   Nothing -> text "unfinish goal" <+> disp g
                                   Just m' -> m'
                               (_, _, [] , m, _) ->
                                 case m of
                                   Nothing -> text "strange" 
                                   Just m' -> m' 
                           ) finals
              in Left $ sep (map (\ (d, i) -> text "Wrong situation" <+> int i $$ nest 2 d)
                             $ zip rs [1..])

env2 = [("H", KArrow Star (KArrow Star Star)), ("J", KArrow Star Star), ("G", KArrow Star Star), ("S", KArrow Star Star)]
exp1 = (Lambda "a1" Nothing
        (Lambda "a2" Nothing
         (Lambda "a3" Nothing
          (App (Var "a3")
           (App (Var "a1")
            (App (Var "a2")
             (App (App (App (Var "h")
                        (Lambda "b1" Nothing (App (Var "a1") (App (Var "a2") (Var "b1")))))
                   (Lambda "b1" Nothing (App (Var "a2") (Var "b1"))))
              (Lambda "b1" Nothing (App (Var "a3") (Var "b1"))))))))))

f1 = Forall "p'" (Forall "f" (Forall "x" (Forall "z" (Imply (Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (PApp (Var "f") (PApp (Const "S") (Var "x"))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "z"))))) (PApp (Var "p") (PApp (PApp (Var "f") (Var "x")) (Var "y"))))))) (Imply (Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (PApp (Const "H") (Var "x")) (PApp (Const "S") (Var "y")))) (PApp (Var "p") (PApp (PApp (Const "H") (PApp (Const "S") (Var "x"))) (Var "y"))))))) (Imply (Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (Const "J") (Var "y"))) (PApp (Var "p") (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "y")))))))) (PApp (Var "p'") (PApp (PApp (Var "f") (PApp (Const "S") (Var "x"))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "z")))))))))))

g2 = PApp (Var "p'") (PApp (PApp (Var "f") (PApp (Const "S") (PApp (Const "S") (Var "x")))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (PApp (Const "S") (Var "z")))))

h2 = PApp (Var "p1fresh") (PApp (PApp (Const "H") (PApp (Const "S") (Var "x2fresh"))) (Var "y3fresh"))
-- initstate1 = [("h", f1, [([], f1, [("h", f1)])], Nothing, 0)]
-- man1 = case [s | s <- construction "h" env2 initstate1 exp1, success s] of
--         (_, pf, _, _, _):_ -> disp pf
-- man3 = construction "h" env2 initstate1 (Var "h")

g1 = PApp (Var "p'") (PApp (PApp (Var "f") (PApp (Const "S") (PApp (Const "S") (Var "x")))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (PApp (Const "S") (Var "z")))))

h1 = PApp (Var "p'1") (PApp (PApp (Var "f2") (PApp (Const "S") (Var "x3"))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x3")) (Var "z4"))))
man2 = runHMatch env2 h1 g1

l1 = PApp (Const "`p8") (PApp (Var "a5") (Const "`y9"))
l2 = PApp (Const "`p8") (PApp (Const "`a0") (PApp (Const "`b1") (Const "`y9")))
tl1 = runHMatch [] l1 l2 --sep [ disp s | s <- evalState (hmatch [] l1 l2) 0] 

success :: ProofState -> Bool
success (ks, gn,pf,[], Nothing, i) = True
success _ = False


display s  = sep [ brackets (sep $ helper q) | (_,_,q ,Nothing, _) <- s ]
helper [] = [empty]
helper ((_,g,_):xs) = disp g : helper xs

-- a wraper on construction just to handle loop better.

      

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
