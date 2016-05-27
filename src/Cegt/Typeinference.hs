module Cegt.Typeinference where

import Cegt.Syntax
import Cegt.Monad

import Cegt.PrettyPrinting
import Cegt.Typecheck
import Control.Monad.State
import Text.PrettyPrint
import Data.List
-- Second order matching, using Gilles Dowek's terminology in his tutorial.
-- generating projection based on kind
genProj :: Kind -> [Exp]
genProj k = let ks = flattenK k
                l = (length ks) - 1
            in if l == 0 then []
               else let vars = map (\ y -> "x"++ show y) $ take l [1..]
                        ts = map (\ z -> foldr (\ x y -> Abs x y) (Var z) vars) vars
                    in ts

genImitation :: Exp -> Kind -> State Int Exp
genImitation (Const h) k = do
                           n <- get
                           let arity = (length (flattenK k)) - 1
                               l = take arity [n..]
                               lb = take arity [1..]
                               n' = n + arity
                               fvars = map (\ x -> "h" ++ show x) l
                               bvars = map (\ x -> "b" ++ show x) lb
                               bvars' = map Var bvars
                               args = map (\ c -> (foldl' (\ z x -> PApp z x) (Var c) bvars')) fvars
                               body = foldl' (\ z x -> PApp z x) (Const h) args
                               res = foldr (\ x y -> Abs x y) body bvars
                           put n'
                           return res

-- list of success: when hmatch success, it returns [Subst]

hmatch :: MonadPlus m => KSubst -> Exp -> Exp -> StateT Int m [Subst]
hmatch ks t1 t2 = do
  let t1' = flatten t1
      t2' = flatten t2'
      (k1, sub1) = runKinding' t1 ks
  case (t1', t2') of
    ((Const x):xs, (Const y):ys) ->
      if x == y then
        do
          bs <- mapM (\ (x, y) -> hmatch ks x y) (zip xs ys)
          let comps = compL bs
              res = concat $ map merge' comps
          return res
      else mzero
    ((Var x):xs, (Const y):ys) -> 
       case (lookup x sub1, lookup y ks) of
         (Nothing, _) -> 

mergeL :: [Subst] -> [Subst]
mergeL l = foldM merge' [] l

merge' :: MonadPlus m => Subst -> Subst -> m Subst
merge' s1 s2 = if agree then return $ nubBy (\ (n1, _) (n2, _) -> n1 == n2 ) (s1 ++ s2) else mzero
  where agree = all (\ x -> applyE s1 (Var x) `alphaEq` applyE s2 (Var x)) (map fst s1 `intersect` map fst s2) 

compL :: [[a]] -> [[a]]
compL l = foldl comph [[]] l

comph :: [[a]] -> [a] -> [[a]]
comph acc l = [ a1 ++ [a2] | a1 <- acc, a2 <- l]


