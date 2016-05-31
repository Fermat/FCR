module Cegt.Interaction where
import Cegt.Syntax
import Cegt.Monad
import Cegt.PrettyPrinting
import Cegt.Typecheck
import Cegt.Rewrite
import Data.List
import Data.Char

import Control.Monad.State
import Text.PrettyPrint
import Debug.Trace

interpret :: Env -> [((Name, Exp), [Tactic])] -> Either Doc [(Name, (Exp, Exp))]
interpret env pfs = do res <- mapM (lemmaConstr env) pfs
                       let as = map (\ ((n, exp),bs) -> (n, exp)) pfs
                           re = zipWith (\ (n1,p1) (n2, ex2) -> (n1, (p1, ex2))) res as
                       return re   
                        
lemmaConstr :: Env -> ((Name, Exp), [Tactic]) -> Either Doc (Name, Exp)
lemmaConstr env ((n, g), ts) =
  let gamma = axioms env ++ map (\ (x,(_,y))-> (x,y)) (lemmas env)
      ks = kinds env
  in
  evalStateT (prfConstr ts) ((n, g, [([], g, gamma)], Nothing, 0), ks)

prfConstr :: [Tactic] -> StateT (ProofState, [(Name, Kind)]) (Either Doc) (Name, Exp)
prfConstr [] = do (ps, _) <- get  -- (Name, Exp, [(Pos, Exp, PfEnv)])
                  case ps of
                    (n, pf, [], Nothing, i) -> return (n, pf)
                    (n, pf, _, Just err, i) -> lift $ Left err
                    (n, pf, (_,g,gamma):as, m, i) ->
                      lift $ Left $ text "unfinished goal" <+> disp g $$
                      text "in the environment" $$ disp gamma
prfConstr (Coind:xs) = do (ps@(n,_,_,_,_), ks) <- get
                          case coind ps of
                            (_,_,_, Just err, _) ->
                              lift $ Left $
                                       text "fail to use coind tactic, in the proof of lemma"
                                       <+> disp n $$ (nest 2 $ disp err)
                            ps'@(_,_,_, Nothing, _) ->
                              put (ps', ks) >> prfConstr xs
                                           
prfConstr ((Intros ns):xs) = do (ps, ks) <- get
                                put (intros ps ns, ks)
                                prfConstr xs

prfConstr ((Apply n ts):xs) = do (ps@(ln,_,_, _, _), ks) <- get
                                 case kindList ts ks of
                                   Left err -> do lift $ Left $
                                                    (text "kinding error:" $$ disp err)
                                   Right _ ->  
                                     case apply ps n ts of
                                       (_,_,_, Just err, _) -> lift $ Left $
                                                  text "fail to use the tactic: apply"
                                                  <+> disp n <+> hcat (map disp ts) $$
                                                  (text "in the proof of lemma" <+> disp ln)
                                                  $$ nest 2 (disp err)
                                             -- <+> text (show ps)
                                       ps'@(_,_,_, Nothing, _) -> put (ps', ks) >> prfConstr xs

prfConstr ((Use n ts):xs) = do (ps@(ln,_,(_,cg,_):_, _, _), ks )<- get  -- (Name, Exp, [(Pos, Exp, PfEnv)])
                               case kindList ts ks of
                                 Left err -> do lift $ Left $
                                                  (text "kinding error:" $$ disp err)
                                 Right _ ->  
                                   case use ps n ts of
                                     (_,_,_, Just err, _) ->
                                       lift $ Left $
                                       text "fail to use the tactic: use"
                                       <+> disp n <+> hcat (map disp ts)
                                       $$ text "in the proof of lemma" <+> disp ln
                                       $$ text "current goal:" <+> disp cg $$
                                       nest 2 (disp err)
                                     ps'@(_,_,_, Nothing, _) -> put (ps', ks) >> prfConstr xs


                            

-- normalize a = error $ show a

-- quantify :: Exp -> ([Name], Exp)
-- quantify a@(Arrow t t') = ("p":(free a), Imply (App (Var "p") t') (App (Var "p") t))

type PfEnv = [(Name, Exp)]
-- (final lemma name, current mix-terms, list of subgoals, error state-nothing means fine, integer state for eigen-var)
type ProofState = (Name, Exp, [(Pos, Exp, PfEnv)], Maybe Doc, Int)

coind :: ProofState -> ProofState
coind (g, pf, ([], pf', env):[], Nothing, i) | pf == pf' =
  (g, pf, ([], pf', env++[(g,pf)]):[], Nothing, i)
                                             | otherwise =
    let err = Just $ text "Inconsistency in the mix proof terms" in
    (g, pf, ([], pf', env):[], err, i)
coind (g, pf, gs, _, i) =
  let err = Just $ text "coind tactic can only be used at the very beginning of the proof" in
  (g, pf, gs, err, i)

intros :: ProofState -> [Name] -> ProofState
intros (gn, pf, [], Nothing, i) ns =
  let err = Just $ text "no more subgoals" in (gn, pf, [], err, i)
intros (gn, pf, (pos, goal, gamma):res, Nothing, i) ns =
  let (vars, head, body) = separate goal
      lb = length body
      lv = length vars
      num = lv + lb
      impNames = ns 
      absNames = zipWith (\ x y -> x ++ show i) vars [i..]
      sub = zip vars (map Const absNames)
      body' = map (\ x -> applyE sub x) body
      head' = applyE sub head
      newEnv = zip impNames body'
      newLam = foldr (\ (a, exp) b -> Lambda a (Just exp) b) head' newEnv
      newAbs = foldr (\ a b -> Lambda a Nothing b) newLam absNames
      pf' = replace pf pos newAbs
      pos' = pos ++ take num stream2
  in (gn, pf', (pos',head', gamma++newEnv):res, Nothing, i+lv)

stream2 = 2:stream2

apply :: ProofState -> Name -> [Exp] -> ProofState
apply (gn, pf, [], Nothing, i) k ins =
  let m' = Just $ text "no more subgoals" in (gn, pf, [], m', i)
apply (gn, pf, (pos, goal, gamma):res, Nothing, i) k ins = 
  case lookup k gamma of
    Nothing -> let m' = Just $ text "can't find" <+> text k <+> text "in the environment" in
      (gn, pf, (pos, goal, gamma):res, m', i)
    Just f -> let (vars, head, body) = separate f
                  i' = i + length vars
                  fresh = map (\ (v, j) -> v ++ show j) $ zip vars [i..]
                  renaming = zip vars (map Var fresh)
                  sub = zip fresh ins
                  body'' = map (applyE renaming) body
                  head'' = applyE renaming head
                  body' = map normalize $ (map (applyE sub) body'')
                  head' = normalize $ applyE sub head''
              in if head' /= goal then
                   let m' = Just $ text "can't match" <+> disp head' <+> text "against"
                            <+> disp goal
                   in
                   (gn, pf, (pos, goal, gamma):res, m', i)
                                       -- error $ "error apply--" ++ show head' ++ "--" ++ show goal
                                       -- ++ show sub ++ "--" ++ show head 
                 else let np = ins -- ++body'
                          name = case k of
                                   n:_ -> if isUpper n then Const k else Var k
                                   a -> error "unknow error from apply"
                          contm = foldl' (\ z x -> App z x) (foldl' (\ z x -> TApp z x) name np)
                                  body'
                          pf' = replace pf pos contm
                          zeros = makeZeros $ length body'
                          ps = map (\ x -> pos++x++[1]) zeros
                          new = map (\(p, g) -> (p, g, gamma)) $ zip ps body'
                      in (gn, pf', new++res, Nothing,i')  

{-
-- smart first order apply for type inference use 
applyF :: ProofState -> Name -> Maybe ProofState
applyF (gn, pf, []) k = Nothing
applyF (gn, pf, (pos, goal, gamma):res) k = 
  case lookup k gamma of
    Nothing -> Nothing
    Just f -> let (vars, head, body) = separate f in
              if null vars then
                if f == goal then
                  let
                    name = case k of
                       n:_ -> if isUpper n then Const k else Var k
                       a -> error "unknow error from applyF"
                    pf' = replace pf pos name
                  in Just (gn, pf', res)  
                else Nothing
              else
                let  
                  fresh = map (\ (v, i) -> v ++ show i ++ "fresh") $ zip vars [1..]
                  renaming = zip vars (map Var fresh)
                  body'' = map (applyE renaming) body
                  head'' = applyE renaming head
                  ss = match head'' goal -- zip fresh ins
                in
                 case ss of
                   Nothing -> Nothing
                   Just sub -> 
                     let body' = map (applyE sub) body''
                         head' = applyE sub head''
                         np = map snd sub  -- ++body'
                         name = case k of
                                 n:_ -> if isUpper n then Const k else Var k
                                 a -> error "unknow error from apply"
                         contm = foldl' (\ z x -> App z x) (foldl' (\ z x -> TApp z x) name np) body'
                         pf' = replace pf pos contm
                         zeros = makeZeros $ length body'
                         ps = map (\ x -> pos++x++[1]) zeros
                         new = map (\(p, g) -> (p, g, gamma)) $ zip ps body'
                     in Just (gn, pf', new++res)  

-}
use :: ProofState -> Name -> [Exp] -> ProofState
use (gn, pf, [], Nothing, i) k ins =
  let m' = Just $ text "no more subgoals" in (gn, pf, [], m', i)
                     
use (gn, pf, (pos, goal, gamma):res, Nothing, i) k ins = 
  case lookup k gamma of
    Nothing ->
      let m' = Just $ text "can't find" <+> text k <+> text "in the environment" in
      (gn, pf, (pos, goal, gamma):res, m', i)
    Just f -> let (vars, bare) = getVars f
                  i' = i + length vars
                  fresh = map (\ (v, j) -> v ++ show j) $ zip vars [i..]
                  renaming = zip vars (map Var fresh)
                  sub = zip fresh ins
                  b'' = applyE renaming bare
                  b' = normalize $ applyE sub b''
                  newVar = permutations $ free b'
                  fs' = [  f1  | vs <- newVar, let f1 = foldl' (\t x -> Forall x t) b' vs,
                             f1 `alphaEq` goal]
              in if null fs' then
                   let m' = Just $ text "can't match" <+> disp f <+> text "against"
                            <+> disp goal
                   in
                    (gn, pf, (pos, goal, gamma):res, m', i)
                 else 
                   let name = case k of
                                   n:_ -> if isUpper n then Const k else Var k
                                   a -> error "unknow error from use"
                       contm = foldl' (\ z x -> TApp z x) name ins
                       pf' = replace pf pos contm
                   in (gn, pf', res, Nothing, i')  

{-
-- smart first order use
useF :: ProofState -> Name -> Maybe ProofState
-- useF init exp | trace (show () ++ "-- " ++show (disp exp)) False = undefined
useF (gn, pf, []) k = Nothing -- error "opps"
useF (gn, pf, (pos, goal, gamma):res) k = 
  case lookup k gamma of
    Nothing -> Nothing
    Just f -> let (vars, bare) = getVars f in
              if null vars then
                if f == goal then
                  let
                    name = case k of
                       n:_ -> if isUpper n then Const k else Var k
                       a -> error "unknow error from useF"
                    pf' = replace pf pos name
                  in Just (gn, pf', res)  
                else Nothing
              else
              let   
                  (varsG, bareG) = getVars goal
                  fresh = map (\ (v, i) -> v ++ show i ++ "fresh") $ zip vars [1..]
                  renaming = zip vars (map Var fresh)
                  b'' = applyE renaming bare
                  ss = match b'' bareG in -- note: useF can not be used if the
                                          -- formula contains quantifiers within its body
              case ss of
                Nothing -> Nothing -- error $ "well" ++ show b'' ++ "--" ++ show bareG -- 
                Just sub -> 
                  let
                    ins = map snd sub
                    b' = applyE sub b''
                    newVar = permutations $ free b'
                    fs' = [  f1  | vs <- newVar, let f1 = foldl' (\t x -> Forall x t) b' vs,
                             f1 `alphaEq` goal]
                  in if null fs' then Nothing
                 else 
                   let name = case k of
                                   n:_ -> if isUpper n then Const k else Var k
                                   a -> error "unknow error from use"
                       contm = foldl' (\ z x -> TApp z x) name ins
                       pf' = replace pf pos contm
                   in Just (gn, pf', res)  
                   
-}                   

separate f = let (vars, imp) = getVars f
                 (bs, h) = getPre imp
             in (vars, h, bs)
                
getVars :: Exp -> ([Name],Exp)
getVars (Forall x t) = let (xs, t') = getVars t in (x:xs, t')
getVars t = ([], t)

getPre ::  Exp -> ([Exp],Exp)
getPre (Imply x y) = let (bs, t') = getPre y in (x:bs, t')
getPre t = ([], t)

-- makeZeros n | trace ("myZeros " ++ show n) False = undefined
makeZeros 0 = []
makeZeros n | n > 0 = make n : makeZeros (n-1)

stream = 0:stream
make n | n > 0 = take (n-1) stream




                                           
                     
                 
                                                    
-- PApp (Var "p'") (PApp (PApp (Var "f") (PApp (Const "S") (Var "x"))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "z"))))
-- PApp (Forall "y" (PApp (Var "p'") (PApp (PApp (Var "f") (PApp (Const "S") (Var "x"))) (Var "y")))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "z")))
{-
ha1 = Imply (Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (PApp (Var "f2fresh") (PApp (Const "S") (Var "x"))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "z4fresh"))))) (PApp (Var "p") (PApp (PApp (Var "f2fresh") (Var "x")) (Var "y"))))))) (Imply (Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (PApp (Const "H") (Var "x")) (PApp (Const "S") (Var "y")))) (PApp (Var "p") (PApp (PApp (Const "H") (PApp (Const "S") (Var "x"))) (Var "y"))))))) (Imply (Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (Const "J") (Var "y"))) (PApp (Var "p") (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "y")))))))) (PApp (Var "p'1fresh") (PApp (PApp (Var "f2fresh") (PApp (Const "S") (Var "x3fresh"))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x3fresh")) (Var "z4fresh")))))))

ha2 = Imply (Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (PApp (Var "f") (PApp (Const "S") (Var "x"))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "z"))))) (PApp (Var "p") (PApp (PApp (Var "f") (Var "x")) (Var "y"))))))) (Imply (Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (PApp (Const "H") (Var "x")) (PApp (Const "S") (Var "y")))) (PApp (Var "p") (PApp (PApp (Const "H") (PApp (Const "S") (Var "x"))) (Var "y"))))))) (Imply (Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (Const "J") (Var "y"))) (PApp (Var "p") (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "y")))))))) (PApp (Var "p'") (PApp (PApp (Var "f") (PApp (Const "S") (Var "x"))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "z"))))))) 
-}
