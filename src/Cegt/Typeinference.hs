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
genImitation head k = do
                           n <- get
                           let arity = (length (flattenK k)) - 1
                               l = take arity [n..]
                               lb = take arity [1..]
                               n' = n + arity
                               fvars = map (\ x -> "h" ++ show x) l
                               bvars = map (\ x -> "b" ++ show x) lb
                               bvars' = map Var bvars
                               args = map (\ c -> (foldl' (\ z x -> PApp z x) (Var c) bvars')) fvars
                               body = foldl' (\ z x -> PApp z x) head args
                               res = foldr (\ x y -> Abs x y) body bvars
                           put n'
                           return res

-- list of success: when hmatch success, it returns [Subst]

hmatch ::  KSubst -> Exp -> Exp -> State Int [Subst]
hmatch ks t1 t2 = do
  let t1' = flatten t1
      t2' = flatten t2
      Right (k1, sub1) = runKinding' t1 ks
      Right (k2, sub2) = runKinding' t2 ks
  case (t1', t2') of
    ((Const x):xs, (Const y):ys) ->
      if x == y then
        do
          bs <- mapM (\ (x, y) -> hmatch ks x y) (zip xs ys)
          let comps = compL bs
              res = concat $ map mergeL comps
          return res
      else return []
    ((Var x):xs, (Const y):ys) ->
      case (lookup x sub1, lookup y (ks++sub2)) of
        (Nothing, _) -> error $ show (text "unkind variable:" <+> text x)
        (_, Nothing) -> error $ show (text "unkind constant:" <+> text y)
        (Just kx, Just ky) ->
          let kx' = ground kx
              ky' = ground ky in
          if kx' == ky' then
            do
              n <- get
              let pjs = genProj kx'
                  (imi, n') = runState (genImitation (Const y) kx') n
                  renew = normalize $ runSubst imi (Var x) t1
                  imiAndProj = (renew, t2) : map (\ x -> (x, t2)) xs
                  oldsubst = [(x, imi)]: map (\ y -> [(x,y)]) pjs
              put n'
              bs <- mapM (\ (x, y) -> hmatch ks x y) imiAndProj
              let
                ps = zip bs oldsubst
                res = map (\ (x, y) -> map (\z -> concat $ merge' z y) x) ps
              return (concat res)
              
          else do
              let proj = map (\ x -> (x, t2)) xs
                  pjs = genProj kx'
                  oldsubst = map (\ y -> [(x,y)]) pjs
              bs <- mapM (\ (x, y) -> hmatch ks x y) proj
              let ps = zip bs oldsubst
                  res = map (\ (x, y) -> map (\z -> concat $ merge' z y) x) ps
              return (concat res)
    ((Var x):xs, (Var y):ys) | x == y ->
        do
          bs <- mapM (\ (x, y) -> hmatch ks x y) (zip xs ys)
          let comps = compL bs
              res = concat $ map mergeL comps
          return res
                             | otherwise ->
          case (lookup x sub1, lookup y (ks++sub2)) of
            (Nothing, _) -> error $ show (text "unkind variable:" <+> text x)
            (_, Nothing) -> error $ show (text "unkind constant:" <+> text y)
            (Just kx, Just ky) ->
              let kx' = ground kx
                  ky' = ground ky in
              if kx' == ky' then
                do
                  n <- get
                  let pjs = genProj kx'
                      (imi, n') = runState (genImitation (Var y) kx') n
                      renew = normalize $ runSubst imi (Var x) t1
                      imiAndProj = (renew, t2) : map (\ x -> (x, t2)) xs
                      oldsubst = [(x, imi)]: map (\ y -> [(x,y)]) pjs
                  put n'
                  bs <- mapM (\ (x, y) -> hmatch ks x y) imiAndProj
                  let
                    ps = zip bs oldsubst
                    res = map (\ (x, y) -> map (\z -> concat $ merge' z y) x) ps
                  return (concat res)
              else do
                let proj = map (\ x -> (x, t2)) xs
                    pjs = genProj kx'
                    oldsubst = map (\ y -> [(x,y)]) pjs
                bs <- mapM (\ (x, y) -> hmatch ks x y) proj
                let ps = zip bs oldsubst
                    res = map (\ (x, y) -> map (\z -> concat $ merge' z y) x) ps
                return (concat res)

    (x, y) -> return [] -- error $ show x ++ show y -- (text "err" <+> disp x <+> disp y <+> disp x' <+> disp y')


            
mergeL :: [Subst] -> [Subst]
mergeL l = foldM merge' [] l

merge' :: MonadPlus m => Subst -> Subst -> m Subst
merge' s1 s2 = if agree then return $ nubBy (\ (n1, _) (n2, _) -> n1 == n2 ) (combine s1 s2) else mzero
  where agree = all (\ x -> applyE s1 (Var x) `alphaEq` applyE s2 (Var x)) (map fst s1 `intersect` map fst s2) 


combine s2 s1 =
   s2 ++ [(v, applyE s2 t) | (v, t) <- s1] 

compL :: [[a]] -> [[a]]
compL l = foldl comph [[]] l

comph :: [[a]] -> [a] -> [[a]]
comph acc l = [ a1 ++ [a2] | a1 <- acc, a2 <- l]

kenv = [("Z", Star), ("S", KArrow Star Star)]
t1 = PApp (Var "p") (PApp (PApp (Var "d") (Const "Z")) (Const "Z"))
t2 = PApp (Var "p1") (PApp (PApp (Var "d") (Const "Z")) (PApp (Const "S") (Const "Z")))
-- hmatch :: MonadPlus m => KSubst -> Exp -> Exp -> StateT Int m [Subst]
-- test1 :: [[Subst]]
test1 = evalState (hmatch kenv t1 t2) 0
  

