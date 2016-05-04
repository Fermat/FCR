module Cegt.Interaction where
import Cegt.Syntax
import Cegt.Rewrite
import Data.List

normalize :: Exp -> Exp
normalize (Var a) = Var a
normalize Star = Star
normalize (Const a) = Const a
normalize (Lambda x t) = Lambda x (normalize t)
normalize (App (Lambda x t') t) = applyE [(x, t)] t'
normalize (App (Var x) t) = App (Var x) (normalize t)
normalize (App (Const x) t) = App (Const x) (normalize t)
normalize (App t' t) = normalize (App (normalize t') (normalize t))
normalize (Imply t t') = Imply (normalize t) (normalize t')
normalize (Forall x t) = Forall x (normalize t)

quantify :: Exp -> ([Name], Exp)
quantify a@(Arrow t t') = ("p":(free a), Imply (App (Var "p") t') (App (Var "p") t))


type ProofState = ([(Name, Exp)], Exp, [(Pos, Exp)])

coind :: Name -> ProofState -> Maybe ProofState
coind n (gamma, pf, ([], pf'):[]) | pf == pf' = Just (gamma++[(n,pf)], pf, ([], pf'):[])
                                  | otherwise = Nothing

intros :: ProofState -> Maybe ProofState
intros (gamma, pf, []) = Just (gamma, pf, [])
intros (gamma, pf, (pos, goal):res) =
  let (vars, head, body) = separate goal
      goal' = head
      num = length vars + length body
      names = map (\ x -> "h"++show x) $ take num [1..]
      newLam = foldr (\ a b -> Lambda a b) head names
      pf' = replace pf pos newLam
      newEnv = zip (drop (length vars) names) body
      pos' = pos ++ take num streamOne in Just (gamma++newEnv, pf', (pos',head):res)

streamOne = 1:streamOne

apply :: ProofState -> Name -> [Exp] -> Maybe ProofState
apply (gamma, pf, []) k ins = Just (gamma, pf, [])
apply (gamma, pf, (pos, goal):res) k ins = 
  case lookup k gamma of
    Nothing -> Nothing
    Just f -> let (vars, head, body) = separate f
                  sub = zip vars ins
                  body' = map normalize $ (map (applyE sub) body)
                  head' = normalize $ applyE sub head
              in if head' /= goal then Nothing
                 else let np = ins++body'
                          contm = foldl' (\ z x -> App z x) (Const k) np
                          pf' = replace pf pos contm
                          zeros = makeZeros $ length body'
                          ps = map (\ x -> pos++x++[1]) zeros
                          new = zip ps body'
                      in Just (gamma, pf', new++res)  

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
                                           
                     
                 
                                                    
