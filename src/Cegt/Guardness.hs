module Cegt.Guardness where
import Cegt.Syntax
import Cegt.Monad
import Cegt.PrettyPrinting
import Cegt.Rewrite

import Data.List
import Data.Char

import Control.Monad.State
import Text.PrettyPrint

alg :: [Name] -> Exp -> Bool
alg vs (Const _) = True
alg vs (Var x) | x `elem` vs = True
alg vs a@(Lambda x _ t) =
  let b = viewLBody a
      freshvars = map fst $ viewLVars a
      b' = flatten b
  in and $ map (alg (freshvars ++ vs)) b'

alg vs a@(App t' t) =
  let b' = flatten a
  in and $ map (alg vs) b'


-- check if f = e is guarded
guardness :: Name -> Exp -> Bool
guardness n e =
                let vars = case e of
                              Lambda _ _ _ -> map fst $ viewLVars e
                              App _ _ -> []
                    vars' = map Var vars
                    body = viewLBody e
                    a = getSubterms e
                    b = [ (pos, t) |  (pos, t) <- a, let c = getHead t, c == (Var n) ]
                    b1 = map snd b
                    b' = [ (pos, t) | (pos, t) <- b, not (or $ map (isSubterm t) b1) ] -- get the largest subterms
                    gpos = do{ (pos, t) <- b'; if null pos then [] else return (init pos ++ [0])}
                    gterms = mapM (retrieve e) gpos
                in case gterms of
                      Nothing -> False
                      Just es -> let ensSet = and $ map (\ x -> case x of
                                                                  Const _ -> True
                                                                  _ -> x `elem` vars') es
                                     cxt = foldr (\ (pos, _) e -> replace e pos (Const "hole")) body b'
                                     args = concat [getArgs a | (_, a) <- b']
                                     alres = and $ map (alg vars) args
                                 in ensSet && alg vars cxt && alres


-- checkHHN n e@(Lambda _ _ _ ) env = True
-- checkHHN n e@(App _ _) env = let a = flatten e
--                              in case a of
--                                   (Var x):[] -> 
