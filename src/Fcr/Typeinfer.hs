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
type ResState = (Name, Exp, [(Pos, Exp, Exp, PfEnv, [Name])], Maybe Doc, Int)

transit :: KSubst -> ResState -> [ResState]

transit ks (gn, pf, (pos, goal@(Imply _ _), exp@(Lambda _ Nothing t), gamma, lvars):phi, Nothing, i) =
  let (bs, h) = getPre goal
      (vars, b) = (map fst $ viewLVars exp, viewLBody exp) in
    if length bs == length vars then
      let newEnv = zip vars bs
          newLam = foldr (\ (a, e) b -> Lambda a (Just e) b) h newEnv
          pf' = replace pf pos newLam
          pos' = pos ++ take (length bs) stream2
      in [(gn, pf', (pos', h, t, gamma++newEnv, lvars):phi, Nothing, i)]
    else  let m' = Just $
                   text "arity mismatch when performing lambda abstraction" $$
                   (nest 2 (text "current goal: " <+> disp goal)) $$ nest 2
                   (text "current program:"<+> disp exp) $$
                   (nest 2 $ text "current mixed proof term" $$ nest 2 (disp pf))
          in [(gn, pf, (pos, goal, exp, gamma, lvars):phi, m', i)]

      
transit ks (gn, pf, (pos, goal@(Forall x y), exp, gamma, lvars):phi, Nothing, i) =
  let (vars, imp) = getVars goal
      lv = length vars
      absNames = zipWith (\ x y -> x ++ show y ++ "'") vars [i..]
      sub = zip vars (map Const absNames)
      imp' = applyE sub imp
      newAbs = foldr (\ a b -> Lambda a Nothing b) imp' absNames
      pf' = replace pf pos newAbs
      pos' = pos ++ take lv stream2
  in [(gn, pf', (pos',imp', exp, gamma, lvars++ absNames):phi, Nothing, i+lv)]

transit ks (gn, pf, (pos, goal, exp@(App p1 p2), gamma, lvars):phi, Nothing, i) =
  case flatten exp of
    (Var v) : xs -> handle v xs
    (Const v) : xs -> handle v xs


  where handle v xs = 
          case lookup v gamma of
            Nothing -> let m' = Just $ text "can't find" <+> text v
                                <+> text "in the environment" in
                         [(gn, pf, (pos, goal, exp, gamma, lvars):phi, m', i)]
            Just f -> let (vars, head, body) = separate f
                          i' = i + length vars
                          fresh = map (\ (v, j) -> v ++ show j ++ "'") $ zip vars [i..]
                          renaming = zip vars (map Var fresh)
                          body'' = map (applyE renaming) body
                          head'' = applyE renaming head
                          ss = runHMatch ks head'' goal
                          lengthCheck = length xs == length body
                      in if lengthCheck then
                           case ss of
                             [] ->
                               let m' = Just $ text "can't match" <+> disp (head'') $$
                                     text "against" <+> disp (goal) $$
                                     (nest 2 (text "when applying" <+>text v <+> text ":"
                                              <+> disp f)) $$
                                     (nest 2 $ text "current mixed proof term" $$
                                      nest 2 (disp pf))
                               in [(gn, pf, (pos, goal, exp, gamma, lvars):phi, m', i)]
                             _ -> do sub <- ss
                                     if scopeCheck lvars sub
                                       then let dom = free head''
                                                body' = map normalize $ (map (applyE sub) body'')
                                                head' = normalize $ applyE sub head''
                                                goodSub = [(x, y) | (x, y) <- sub, x `elem` dom ]
                                                np = ([ s | r <- fresh,
                                                        let s = case lookup r sub of
                                                                  Nothing -> (Var r)
                                                                  Just t -> t]) 
                                                lvars' = (lvars \\ (map fst goodSub)) ++
                                                         [ x | x <- fresh, not (x `elem` dom)]
                                                contm = foldl' (\ z x -> App z x)
                                                        (foldl' (\ z x -> TApp z x) (Var v) np)
                                                        body'
                                                pf' = normEvidence $ applyE goodSub pf
                                                pf'' = replace pf' pos contm
                                                zeros = makeZeros $ length body'
                                                ps = map (\ x -> pos++x++[1]) zeros
                                                gamma' = map
                                                         (\(x, y) ->
                                                             (x, normalize $ applyE goodSub y))
                                                         gamma
                                                (high, low) = arrange $ zip (zip ps body') xs
                                                (high', low') = (map (\((p, g),e ) -> (p, g, e, gamma', lvars')) high, map (\((p, g), e ) -> (p, g, e, gamma', lvars')) low)
                                                phi' = applyPhi goodSub phi in
                                              case phi' of
                                                Just p -> return
                                                          (gn, pf'', high'++p++low', Nothing, i')
                                                Nothing ->
                                                  let m' = Just $
                                                           text "scope error when matching" <+>
                                                           disp (head'') $$ text "against"
                                                           <+> disp (goal) $$
                                                           (nest 2 (text "when applying" <+>text v <+> text ":" <+> disp f)) $$ (nest 2 $ text "current mixed proof term" $$ nest 2 (disp pf)) in
                                                    [(gn, pf, (pos, goal, exp, gamma, lvars):phi, m', i)]
                                       else let m' = Just $
                                                     text "scope error when matching" <+>
                                                     disp (head'') $$ text "against"
                                                     <+> disp (goal) $$
                                                     (nest 2 (text "when applying" <+>text v <+> text ":" <+> disp f)) $$ (nest 2 $ text "current mixed proof term" $$ nest 2 (disp pf)) in
                                       [(gn, pf, (pos, goal, exp, gamma, lvars):phi, m', i)]
                            
                         else let m' = Just $
                                    text "arity mismatch when performing application" $$
                                    (nest 2 (text "current goal: " <+> disp goal)) $$ nest 2
                                    (text "current program:"<+> disp exp) $$
                                    (nest 2 (text "when using formula:"<+> disp f)) $$
                                    (nest 2 $ text "current mixed proof term" $$ nest 2 (disp pf))
                              in [(gn, pf, (pos, goal, exp, gamma, lvars):phi, m', i)]

transit ks s = [s]

ersm :: [ResState] -> KSubst -> Either Doc Exp
ersm init ks = let s = concat $ map (transit ks) init
                   (pending, fails) = partition failure s
                   flag = length fails == length s
               in if flag then
                    let rs = map (\(_,_,_, Just m, _) -> m) fails in
                      Left $ sep (map (\ (d, i) -> text "Wrong situation" <+> int i $$ nest 2 d)
                                   $ zip rs [1..])
                  else case [p | p <- pending, success p ] of
                         [] -> ersm s ks
                         (_, pf, _, _, _):_ -> Right pf
                             
  where failure (_,_, _, Just _,_) = True
        failure _ = False
        success (gn,pf,[], Nothing, i) = True
        success _ = False


        
arrange :: [((Pos, Exp), Exp)] -> ([((Pos, Exp), Exp)], [((Pos, Exp), Exp)])
arrange ls = partition (\((p,f),e) -> (not $ null (free f))) ls
                 

applyPhi :: [(Name, Exp)] -> [(Pos, Exp, Exp, PfEnv, [Name])] ->
            Maybe [(Pos, Exp, Exp, PfEnv, [Name])]
applyPhi sub ls = let f = and [scopeCheck lvars sub | (p, g, e, env, lvars) <- ls]
                      ls' = map (\(p, g, e, env, lvars) ->
                                    (p, normalize $ applyE sub g, e,
                                     map (\ (x, t) -> (x, normalize $ applyE sub t)) env,
                                     lvars \\ map fst sub)) ls
                  in if f then Just ls'
                       else Nothing
        
scopeCheck :: [Name] -> [(Name, Exp)] -> Bool
scopeCheck lvars sub = let (sub1, sub2) = partition (\(x, t) -> x `elem` lvars) sub
                           r1 = and [ null (rvars `intersect` b) | (x, t) <- sub1,
                                      let (a, b) = break (== x) lvars, let rvars = free t]
                           r2 = and [null r | (x, t) <- sub2, let r = free t `intersect` lvars]
                       in r1 && r2

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
