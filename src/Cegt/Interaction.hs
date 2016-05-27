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
  evalStateT (prfConstr ts) ((n, g, [([], g, gamma)]), ks)

prfConstr :: [Tactic] -> StateT (ProofState, [(Name, Kind)]) (Either Doc) (Name, Exp)
prfConstr [] = do (ps, _) <- get  -- (Name, Exp, [(Pos, Exp, PfEnv)])
                  case ps of
                    (n, pf, []) -> return (n, pf)
                    (n, pf, (_,g,gamma):as) -> lift $ Left $ text "unfinished goal" <+> disp g $$
                                           text "in the environment" $$ disp gamma
prfConstr (Coind:xs) = do (ps@(n,_,_), ks) <- get
                          case coind ps of
                            Nothing -> lift $ Left $
                                       text "fail to use coind tactic, in the proof of lemma"
                                       <+> disp n
                            Just ps' -> put (ps', ks) >> prfConstr xs
                                           
prfConstr ((Intros ns):xs) = do (ps, ks) <- get
                                put (intros ps ns, ks)
                                prfConstr xs

prfConstr ((Apply n ts):xs) = do (ps@(ln,_,_), ks) <- get
                                 case kindList ts ks of
                                   Left err -> do lift $ Left $
                                                    (text "kinding error:" $$ disp err)
                                   Right _ ->  
                                     case apply ps n ts of
                                       Nothing -> lift $ Left $
                                                  text "fail to use the tactic: apply"
                                                  <+> disp n <+> hcat (map disp ts) $$
                                                  text "in the proof of lemma" <+> disp ln
                                             -- <+> text (show ps)
                                       Just ps' -> put (ps', ks) >> prfConstr xs

prfConstr ((Use n ts):xs) = do (ps@(ln,_,(_,cg,_):_), ks )<- get  -- (Name, Exp, [(Pos, Exp, PfEnv)])
                               case kindList ts ks of
                                 Left err -> do lift $ Left $
                                                  (text "kinding error:" $$ disp err)
                                 Right _ ->  
                                   case use ps n ts of
                                     Nothing -> lift $ Left $
                                                text "fail to use the tactic: use"
                                                <+> disp n <+> hcat (map disp ts)
                                                $$ text "in the proof of lemma" <+> disp ln
                                                $$ text "current goal:" <+> disp cg
                                     Just ps' -> put (ps', ks) >> prfConstr xs


                            

-- normalize a = error $ show a

-- quantify :: Exp -> ([Name], Exp)
-- quantify a@(Arrow t t') = ("p":(free a), Imply (App (Var "p") t') (App (Var "p") t))

type PfEnv = [(Name, Exp)]
type ProofState = (Name, Exp, [(Pos, Exp, PfEnv)])

coind :: ProofState -> Maybe ProofState
coind (g, pf, ([], pf', env):[]) | pf == pf' = Just (g, pf, ([], pf', env++[(g,pf)]):[])
                                 | otherwise = Nothing
coind _ = Nothing

intros :: ProofState -> [Name] -> ProofState
intros (gn, pf, []) ns = (gn, pf, [])
intros (gn, pf, (pos, goal, gamma):res) ns =
  let (vars, head, body) = separate goal
      goal' = head
      lb = length body
      lv = length vars
      num = lv + lb
      impNames = ns -- drop lv ns 
      absNames = vars -- take lv ns
      newEnv = zip impNames body
      newLam = foldr (\ (a, exp) b -> Lambda a (Just exp) b) head newEnv
      newAbs = foldr (\ a b -> Lambda a Nothing b) newLam absNames
      pf' = replace pf pos newAbs
      pos' = pos ++ take num stream2 in (gn, pf', (pos',head, gamma++newEnv):res)

stream2 = 2:stream2

apply :: ProofState -> Name -> [Exp] -> Maybe ProofState
apply (gn, pf, []) k ins = Just (gn, pf, [])
apply (gn, pf, (pos, goal, gamma):res) k ins = 
  case lookup k gamma of
    Nothing -> Nothing
    Just f -> let (vars, head, body) = separate f
                  fresh = map (\ (v, i) -> v ++ show i ++ "fresh") $ zip vars [1..]
                  renaming = zip vars (map Var fresh)
                  sub = zip fresh ins
                  body'' = map (applyE renaming) body
                  head'' = applyE renaming head
                  body' = map normalize $ (map (applyE sub) body'')
                  head' = normalize $ applyE sub head''
              in if head' /= goal then Nothing
                                       -- error $ "error apply--" ++ show head' ++ "--" ++ show goal
                                       -- ++ show sub ++ "--" ++ show head 
                 else let np = ins -- ++body'
                          name = case k of
                                   n:_ -> if isUpper n then Const k else Var k
                                   a -> error "unknow error from apply"
                          contm = foldl' (\ z x -> App z x) (foldl' (\ z x -> TApp z x) name np) body'
                          pf' = replace pf pos contm
                          zeros = makeZeros $ length body'
                          ps = map (\ x -> pos++x++[1]) zeros
                          new = map (\(p, g) -> (p, g, gamma)) $ zip ps body'
                      in Just (gn, pf', new++res)  

-- smart first order apply for type inference use 
applyF :: ProofState -> Name -> Maybe ProofState
applyF (gn, pf, []) k = Nothing
applyF (gn, pf, (pos, goal, gamma):res) k = 
  case lookup k gamma of
    Nothing -> Nothing
    Just f -> let (vars, head, body) = separate f
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


use :: ProofState -> Name -> [Exp] -> Maybe ProofState
use (gn, pf, []) k ins = Just (gn, pf, [])
use (gn, pf, (pos, goal, gamma):res) k ins = 
  case lookup k gamma of
    Nothing -> Nothing
    Just f -> let (vars, bare) = getVars f
                  fresh = map (\ (v, i) -> v ++ show i ++ "fresh") $ zip vars [1..]
                  renaming = zip vars (map Var fresh)
                  sub = zip fresh ins
                  b'' = applyE renaming bare
                  b' = normalize $ applyE sub b''
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
