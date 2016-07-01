module Fcr.Guardness where
import Fcr.Syntax
import Fcr.Monad
import Fcr.PrettyPrinting
import Fcr.Rewrite

import Data.List
import Data.Char

import Control.Monad.State
import Text.PrettyPrint
import Debug.Trace
-- alg binder forbid
alg :: [Name] -> [Name] -> Exp -> Bool
-- alg ks fb exp | trace (show (ks) ++ "-- " ++show (disp exp)) False = undefined
alg vs fb (Const _) = True
alg vs fb (Var x) | x `elem` fb = False
                  | otherwise = True
-- alg vs (Var x) | x `elem` vs = True
--                | otherwise = error $ "from alg" ++ show vs ++ show x
alg vs fb a@(Lambda _ _ t) =
  let b = viewLBody a
      freshvars = map fst $ viewLVars a
      b' = flatten b
  in case b' of
       (Var x):xs | not (x `elem` (freshvars ++ vs))  -> and $ map (alg (freshvars ++ vs) fb) xs
                  | otherwise -> False -- error "ha1"
       (Const x):xs -> and $ map (alg (freshvars ++ vs) fb) xs
       _ -> False -- error "ha2" 
alg vs fb a@(App _ _) =
  let b' = flatten a
  in case b' of
       (Var x):xs | not (x `elem` vs)  -> and $ map (alg vs fb) xs
                  | otherwise -> False -- error $ "ha3" ++ show x ++ show xs 
       (Const x):xs -> and $ map (alg vs fb) xs
       _ -> False -- error "ha4" 


-- alg vs a@(App t' t) =
--   let b' = flatten a
--   in and $ map (alg vs) b'


-- check if f = e is guarded
guardness :: Name -> Exp -> Bool
guardness n e =
                let vars = case e of
                              Lambda _ _ _ -> map fst $ viewLVars e
                              _ -> []
                    vars' = map Var vars
                    body = case e of
                              Lambda _ _ _ -> viewLBody e
                              _ -> e
                    a = getSubterms body
                    b = [ (pos, t) |  (pos, t) <- a, let c = getHead t, c == (Var n) ]
                    b1 = map snd b
                    b' = [ (pos, t) | (pos, t) <- b, not (or $ map (isSubterm t) b1) ] -- get the largest subterms
                    gpos = [p | (pos, t) <- b',
                            let p = if null pos then Nothing else Just (init pos ++ [0])]
                    gpos' = mapM id gpos
                in
                 case gpos' of
                   Nothing -> False -- error "wow1"-- 
                   Just gpos'' -> 
                     case mapM (retrieve body) gpos'' of
                      Nothing -> False --error "wow2" -- 
                      Just es -> let ensSet = and $ map (\ x -> case flatten x of
                                                                  (Const _):_ -> True
                                                                  (Var y):_ -> y `elem` vars
                                                                  _ -> False
                                                        ) es
                                     cxt = foldr (\ (pos, _) e ->
                                                   replace e pos (Const "hole")) body b'
                                     args = concat [getArgs a | (_, a) <- b']
                                     alres = and $ map (alg [] [n]) args
                                 in ensSet && alg [] [] cxt && alres



-- checkHHN n e@(Lambda _ _ _ ) env = guardness n e
-- checkHHN n e@(App _ _) env = let a = flatten e
--                              in case a of
--                                   (Var x):[] -> 
