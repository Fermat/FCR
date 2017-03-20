module Fcr.Typeinfer where

import Fcr.Syntax
import Fcr.Monad
import Fcr.Rewrite hiding (merge')
import Fcr.PrettyPrinting
import Fcr.Typecheck
import Debug.Trace
import Control.Monad.State
import Text.PrettyPrint
import Data.List
import Data.Char
import Debug.Trace
import qualified Data.Set as S
-- [(Var|Const : Types)]
type PfEnv = [(Name, Exp)]

-- (Kind info, global name for the proof, Mixed proof and goals,
--    [(position, current goal, current program, Environment, Scope list)],
--      Error message, counter for generating new variable during the resolution)
type ResState = (KSubst, Name, Exp, [(Pos, Exp, Exp, PfEnv, [Name])], Maybe Doc, Int)

transit :: ResState -> [ResState]

transit (ks, gn, pf, (pos, goal@(Imply _ _), exp@(Lambda _ Nothing t), gamma, lvars):phi, Nothing, i) =
  let (bs, h) = getPre goal
      (vars, b) = (map fst $ viewLVars exp, viewLBody exp) in
    if length bs == length vars then
      let newEnv = zip vars bs
          newLam = foldr (\ (a, e) b -> Lambda a (Just e) b) h newEnv
          pf' = replace pf pos newLam
          pos' = pos ++ take (length bs) stream2
      in [(ks, gn, pf', (pos', h, b, gamma++newEnv, lvars):phi, Nothing, i)]
    else  let m' = Just $
                   text "arity mismatch when performing lambda abstraction" $$
                   (nest 2 (text "current goal: " <+> disp goal)) $$ nest 2
                   (text "current program:"<+> disp exp) $$
                   (nest 2 $ text "current mixed proof term" $$ nest 2 (disp pf))
          in [(ks, gn, pf, (pos, goal, exp, gamma, lvars):phi, m', i)]

      
transit (ks, gn, pf, (pos, goal@(Forall x y), Const v, gamma, lvars):phi, Nothing, i) =
  case lookup v gamma of
    Just f -> 
      if f `alphaEq` goal then
        let name = if (isUpper $ Data.List.head v)
                   then Const v else Var v
            pf' = replace pf pos name in
          [(ks, gn, pf', phi, Nothing, i)]
      else 
        let (vars, imp) = getVars goal
            lv = length vars
            absNames = zipWith (\ x y -> x ++ show y ++ "'") vars [i..]
            sub = zip vars (map Const absNames)
            imp' = applyE sub imp
            newAbs = foldr (\ a b -> Lambda a Nothing b) imp' absNames
            pf' = replace pf pos newAbs
            pos' = pos ++ take lv stream2
        in [(ks, gn, pf', (pos',imp', Const v, gamma, lvars++ absNames):phi, Nothing, i+lv)]
    Nothing -> let m' = Just $ text "can't find" <+> text v
                        <+> text "in the environment" in
                 [(ks, gn, pf, (pos, goal, Const v, gamma, lvars):phi, m', i)]

transit (ks, gn, pf, (pos, goal@(Forall x y), Var v, gamma, lvars):phi, Nothing, i) =
  case lookup v gamma of
    Just f -> 
      if f `alphaEq` goal then
        let name = if (isUpper $ Data.List.head v)
                   then Var v else Var v
            pf' = replace pf pos name in
          [(ks, gn, pf', phi, Nothing, i)]
      else 
        let (vars, imp) = getVars goal
            lv = length vars
            absNames = zipWith (\ x y -> x ++ show y ++ "'") vars [i..]
            sub = zip vars (map Var absNames)
            imp' = applyE sub imp
            newAbs = foldr (\ a b -> Lambda a Nothing b) imp' absNames
            pf' = replace pf pos newAbs
            pos' = pos ++ take lv stream2
        in [(ks, gn, pf', (pos',imp', Var v, gamma, lvars++ absNames):phi, Nothing, i+lv)]
    Nothing -> let m' = Just $ text "can't find" <+> text v
                        <+> text "in the environment" in
                 [(ks, gn, pf, (pos, goal, Var v, gamma, lvars):phi, m', i)]

transit (ks, gn, pf, (pos, goal@(Forall x y), exp, gamma, lvars):phi, Nothing, i) =
  let (vars, imp) = getVars goal
      lv = length vars
      absNames = zipWith (\ x y -> x ++ show y ++ "'") vars [i..]
      sub = zip vars (map Const absNames)
      imp' = applyE sub imp
      newAbs = foldr (\ a b -> Lambda a Nothing b) imp' absNames
      pf' = replace pf pos newAbs
      pos' = pos ++ take lv stream2
  in [(ks, gn, pf', (pos',imp', exp, gamma, lvars++ absNames):phi, Nothing, i+lv)]

transit (ks, gn, pf, (pos, goal, exp, gamma, lvars):phi, Nothing, i) =
  case flatten exp of
    (Var v) : xs -> handle v xs
    (Const v) : xs -> handle v xs
    a -> error $ "hey " ++ show (disp exp)

  where handle v xs = 
          case lookup v gamma of
            Nothing -> let m' = Just $ text "can't find" <+> text v
                                <+> text "in the environment" in
                         [(ks, gn, pf, (pos, goal, exp, gamma, lvars):phi, m', i)]
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
                               let m' = Just $ text "can't match" <+> disp head'' $$
                                        text "against" <+> disp goal $$
                                        (nest 2 (text "when applying" <+>text v <+> text ":"
                                                 <+> disp f)) $$
                                        (nest 2 $ text "current mixed proof term" $$
                                         nest 2 (disp pf))
                               in [(ks, gn, pf, (pos, goal, exp, gamma, lvars):phi, m', i)]
                             _ -> do sub <- ss
                                     let subFCheck = [(x, y)|(x, y) <- sub, not $ x `elem` fresh]
                                     if scopeCheck lvars subFCheck
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
                                                -- lvars' = (lvars ++ fresh)\\ (map fst goodSub)
                                                name = if isUpper $ Data.List.head v
                                                       then Const v else Var v
                                                contm = foldl' (\ z x -> App z x)
                                                        (foldl' (\ z x -> TApp z x) name np)
                                                        body'
                                                pf' = normEvidence $ applyE subFCheck pf
                                                pf'' = replace pf' pos contm
                                                zeros = makeZeros $ length body'
                                                ps = map (\ x -> pos++x++[1]) zeros
                                                gamma' = map
                                                         (\(x, y) ->
                                                             (x, normalize $ applyE goodSub y))
                                                         gamma
                                                (high, low) = arrange $ zip (zip ps body') xs
                                                (high', low') = (map (\((p, g),e ) -> (p, g, e, gamma', lvars')) high, map (\((p, g), e ) -> (p, g, e, gamma', lvars')) low)
                                                phi' = applyPhi subFCheck phi in
                                              case phi' of
                                                Just p -> return
                                                          (ks, gn, pf'', high'++low'++p, Nothing, i')
                                                Nothing ->
                                                  let mess = text "environmental scope error when matching"
                                                               <+> disp (head'') $$
                                                                    text "against"<+> disp (goal)
                                                                     $$ (nest 2 (text "when applying" <+> text v <+> text ":" <+> disp f)) $$ (nest 2 (text "when applying substitution" <+> text "[" <+> disp goodSub <+> text "]")) $$ (nest 2 $ text "The current local vars:" $$ nest 2 (hsep $ map text lvars')) $$ (nest 2 $ text "The current mixed proof term" $$ nest 2 (disp pf))
                                                    in [(ks, gn, pf, (pos, goal, exp, gamma, lvars):phi, Just mess, i)]
                                       else
                                       let mess = text "scope error when matching"
                                                  <+> disp (head'') $$
                                                  text "against"<+> disp (goal)
                                                  $$ (nest 2 (text "when applying" <+> text v <+> text ":" <+> disp f)) $$ (nest 2 (text "when applying substitution" <+> text "[" <+> disp sub <+> text "]")) $$ (nest 2 $ text "to the current mixed proof term" $$ nest 2 (disp pf))
                                       in [(ks, gn, pf, (pos, goal, exp, gamma, lvars):phi, Just mess, i)]
                         else
                           if f `alphaEq` goal then
                                     let name = if (isUpper $ Data.List.head v)
                                                then Const v else Var v
                                         pf' = replace pf pos name in
                                       [(ks, gn, pf', phi, Nothing, i)]
                           else 
                             let m' = Just $
                                      text "arity mismatch when performing application" $$
                                      (nest 2 (text "current goal: " <+> disp goal)) $$ nest 2
                                      (text "current program:"<+> disp exp) $$
                                      (nest 2 (text "when using formula:"<+> disp f)) $$
                                      (nest 2 $ text "current mixed proof term" $$ nest 2 (disp pf))
                             in [(ks, gn, pf, (pos, goal, exp, gamma, lvars):phi, m', i)]

-- transit (ks, gn, pf, (pos, goal, exp, gamma, lvars):phi, Nothing, i) =
--   case exp of
--     Var v -> handle v
--     Const v -> handle v
--   where handle v = case lookup v gamma of
--                          Nothing -> let m' = Just $ text "can't find" <+> text v
--                                           <+> text "in the environment" in
--                                       [(ks, gn, pf, (pos, goal, exp, gamma, lvars):phi, m', i)]
--                          Just f -> if f `alphaEq` goal then
--                                      let name = if (isUpper $ head v) then Const v else Var v
--                                          pf' = replace pf pos name in
--                                        [(ks, gn, pf', phi, Nothing, i)]
--                                    else
                                     
--                                      let m' = Just $ text "can't match" <+> disp f $$
--                                               text "against" <+> disp goal $$
--                                               (nest 2 (text "when applying" <+>text v <+> text ":"
--                                                         <+> disp f)) $$
--                                               (nest 2 $ text "current mixed proof term" $$
--                                                nest 2 (disp pf))
--                                      in [(ks, gn, pf, (pos, goal, exp, gamma, lvars):phi, m', i)]



  
transit s = [s]

ersm :: [ResState] -> Either Doc Exp
-- ersm n | trace ("ersm " ++ show n) False = undefined
ersm init = let s = concat $ map transit init
                (fails, pending) = partition failure s
                flag = length fails == length s
            in if flag then
                 let rs = map (\(_, _,_,_, Just m, _) -> m) fails in
                   Left $ sep (map (\ (d, i) -> text "Wrong situation" <+> int i $$ nest 2 d)
                                $ zip rs [1..])
               else case [p | p <- pending, success p ] of
                      [] -> ersm s 
                      (_, _, pf, _, _, _):_ -> Right pf
                             
  where failure (_, _,_, _, Just _,_) = True
        failure _ = False
        success (_, gn,pf,[], Nothing, i) = True
        success _ = False


        
arrange :: [((Pos, Exp), Exp)] -> ([((Pos, Exp), Exp)], [((Pos, Exp), Exp)])
arrange ls =  partition helper ls
  where helper ((p,f),e) = let (vars, h, _) = separate f
                               fr = free f
                           in null (fr `intersect` (free h))
                 

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
                                      let (a, b) = break (== x) lvars, let rvars = free' t]
                           r2 = and [null r | (x, t) <- sub2, let r = free' t `intersect` lvars]
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
