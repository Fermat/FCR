module Cegt.Interaction where
import Cegt.Syntax
import Cegt.PrettyPrinting
import Cegt.Rewrite
import Data.List
import Data.Char

normalize :: Exp -> Exp
normalize (Var a) = Var a
-- normalize Star = Star
normalize (Const a) = Const a
normalize (Lambda x t) = Lambda x (normalize t)
normalize (App (Lambda x t') t) = runSubst t (Var x) t'
normalize (App (Var x) t) = App (Var x) (normalize t)
normalize (App (Const x) t) = App (Const x) (normalize t)
normalize (App t' t) = case (App (normalize t') (normalize t)) of
                              a@(App (Lambda x t') t) -> normalize a
                              b -> b
normalize (Imply t t') = Imply (normalize t) (normalize t')
normalize (Forall x t) = Forall x (normalize t)
-- normalize a = error $ show a

quantify :: Exp -> ([Name], Exp)
quantify a@(Arrow t t') = ("p":(free a), Imply (App (Var "p") t') (App (Var "p") t))

type PfEnv = [(Name, Exp)]
type ProofState = (Name, Exp, [(Pos, Exp, PfEnv)])

coind :: ProofState -> Maybe ProofState
coind (g, pf, ([], pf', env):[]) | pf == pf' = Just (g, pf, ([], pf', env++[(g,pf)]):[])
                                 | otherwise = Nothing

intros :: ProofState -> [Name] -> ProofState
intros (gn, pf, []) ns = (gn, pf, [])
intros (gn, pf, (pos, goal, gamma):res) ns =
  let (vars, head, body) = separate goal
      goal' = head
      lb = length body
      lv = length vars
      num = lv + lb
      impNames = drop lv ns 
      names = ns 
      newLam = foldr (\ a b -> Lambda a b) head names
      pf' = replace pf pos newLam
      newEnv = zip impNames body
      pos' = pos ++ take num streamOne in (gn, pf', (pos',head, gamma++newEnv):res)

streamOne = 1:streamOne

apply :: ProofState -> Name -> [Exp] -> Maybe ProofState
apply (gn, pf, []) k ins = Just (gn, pf, [])
apply (gn, pf, (pos, goal, gamma):res) k ins = 
  case lookup k gamma of
    Nothing -> Nothing
    Just f -> let (vars, head, body) = separate f
                  sub = zip vars ins
                  body' = map normalize $ (map (applyE sub) body)
                  head' = normalize $ applyE sub head
              in if head' /= goal then Nothing
                 else let np = ins++body'
                          name = case k of
                                   n:_ -> if isUpper n then Const k else Var k
                                   a -> error "unknow error from apply"
                          contm = foldl' (\ z x -> App z x) name np
                          pf' = replace pf pos contm
                          zeros = makeZeros $ length body'
                          ps = map (\ x -> pos++x++[1]) zeros
                          new = map (\(p, g) -> (p, g, gamma)) $ zip ps body'
                      in Just (gn, pf', new++res)  

separate f = let (vars, imp) = getVars f
                 (bs, h) = getPre imp
             in (vars, h, bs)
                
getVars :: Exp -> ([Name],Exp)
getVars (Forall x t) = let (xs, t') = getVars t in (x:xs, t')
getVars t = ([], t)

getPre ::  Exp -> ([Exp],Exp)
getPre (Imply x y) = let (bs, t') = getPre y in (x:bs, t')
getPre t = ([], t)

makeZeros 0 = []
makeZeros n | n > 0 = make n : makeZeros (n-1)
stream = 0:stream
make n | n > 0 = take (n-1) stream


-- test1 = apply gamma1 "h2" [Const "Z"]
-- gamma1 = ([("h1",Forall "x" (Forall "y" (Imply (App (App (Var "d") (Var "x")) (App (Const "S") (Var "y"))) (App (App (Var "d") (App (Const "S") (Var "x"))) (Var "y"))))),("h2",Forall "y" (Imply (App (App (Var "d") (App (Const "S") (Var "y"))) (Const "Z")) (App (App (Var "d") (Const "Z")) (Var "y"))))],Lambda "d" (Lambda "h1" (Lambda "h2" (App (App (Var "d") (Const "Z")) (Const "Z")))),[([1,1,1],App (App (Var "d") (Const "Z")) (Const "Z"))])

-- gamma2 = 
-- test2 = disp $ normalize $ applyE [("d", (Lambda "x" (Lambda "y" (App (App (Var "d") (Var "x")) (App (Const "S") (Var "y"))))))] (Imply (Forall "y" (Imply (App (App (Var "d") (App (Const "S") (Var "y"))) (Const "Z")) (App (App (Var "d") (Const "Z")) (Var "y")))) (App (App (Var "d") (Const "Z")) (Const "Z")))
{-
apply :: Exp -> Exp -> [(Name, Exp)] -> Name -> [Exp] -> Maybe Exp
apply goal cxt env k ins = case lookup k env of
                             Nothing -> Nothing
                             Just (Arrow t t') -> let (xs, Imply e e') = quantify $ Arrow t t'
                                                      sub = zip xs ins
                                                      body = normalize $ applyE sub e
                                                      head = normalize $ applyE sub e'
                                                  in if head == goal then Just $ () body
                                                     else Nothing





resolve :: Exp -> [(Name, Exp)] -> Name -> Maybe Exp
resolve goal env k = case lookup k env of
                           Nothing -> Nothing
                           Just (Arrow t t') ->
                             let (vars, Imply e e') = quantify $ Arrow t t'
                                 instCxt = [(p, s) | (p, e) <- getSubterms goal, s <- match t e, s /= []]
                             in case instCxt of
                               [] -> Nothing
                               (p,ins):xs ->
                                 let
                                   cxt = ("p", Lambda "y" (replace e p (Var "y")))
                                   sub = cxt:ins
                                   sub' = helper sub vars
                                   body = normalize $ applyE sub' e
                                   head = normalize $ applyE sub' e'
                                 in Just body
                     where helper s [] = []
                           helper s (y:ys) = case lookup y s of
                                                   Nothing -> (y, Var y) : helper s ys
                                                   Just t -> (y, t) :helper s ys
-}                                        
                                           
                     
                 
                                                    
