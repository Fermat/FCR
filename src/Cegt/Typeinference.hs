module Cegt.Typeinference where

import Cegt.Syntax
import Cegt.Monad

import Cegt.PrettyPrinting
import Cegt.Typecheck
import Control.Monad.State
import Text.PrettyPrint
import Data.List
import Debug.Trace
-- Second order matching, using Gilles Dowek's terminology in his tutorial.
-- generating projection based on kind
genProj :: Kind -> [Exp]
genProj k = let ks = flattenK k
                l = (length ks) - 1
            in if l == 0 then []
               else let vars = map (\ y -> "x"++ show y) $ take l [1..]
                        ts = map (\ z -> foldr (\ x y -> Abs x y) (Var z) vars) vars
                    in ts

-- k1 is for kind of head, k2 is for the kind
genImitation :: Exp -> Kind -> Kind -> State Int Exp
genImitation head k1 k2 = do
                           n <- get
                           let arity = (length (flattenK k2)) - 1
                               arity' = (length (flattenK k1)) - 1 
                               l = take arity' [n..]
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
-- hmatch ks t1 t2 | trace (show (disp t1) ++ "-- " ++show (disp t2)) False = undefined
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
            do
              n <- get
              let pjs = genProj kx'
                  (imi, n') = runState (genImitation (Const y) ky' kx') n
                  renew = normalize $ runSubst imi (Var x) t1
                  imiAndProj = (renew, t2) : map (\ x -> (x, t2)) xs
                  oldsubst = [(x, imi)]: map (\ y -> [(x,y)]) pjs
              put n'
              bs <- mapM (\ (x, y) -> hmatch ks x y) imiAndProj
              let
                ps = zip bs oldsubst
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
                do
                  n <- get
                  let pjs = genProj kx'
                      (imi, n') = runState (genImitation (Var y) ky' kx') n
                      renew = normalize $ runSubst imi (Var x) t1
                      imiAndProj = (renew, t2) : map (\ x -> (x, t2)) xs
                      oldsubst = [(x, imi)]: map (\ y -> [(x,y)]) pjs
                  put n'
                  bs <- mapM (\ (x, y) -> hmatch ks x y) imiAndProj
                  let
                    ps = zip bs oldsubst
                    res = map (\ (x, y) -> map (\z -> concat $ merge' z y) x) ps
                  return (concat res)

    (x, y) -> return [] -- error $ show x ++ show y -- (text "err" <+> disp x <+> disp y <+> disp x' <+> disp y')


            
mergeL :: [Subst] -> [Subst]
mergeL l = foldM merge' [] l

merge' :: MonadPlus m => Subst -> Subst -> m Subst
merge' s1 s2 = if agree then return $ nubBy (\ (n1, _) (n2, _) -> n1 == n2 ) (combine s1 s2) else mzero
  where agree = all (\ x -> applyE s1 (Var x) `alphaEq` applyE s2 (Var x)) (map fst s1 `intersect` map fst s2) 


combine s2 s1 =
   s2 ++ [(v, normalize $ applyE s2 t) | (v, t) <- s1] 

compL :: [[a]] -> [[a]]
compL l = foldl comph [[]] l

comph :: [[a]] -> [a] -> [[a]]
comph acc l = [ a1 ++ [a2] | a1 <- acc, a2 <- l]


wellKind :: [Name] -> KSubst -> [Subst] -> [Subst]
wellKind vs ks subs = [ s | s <- subs, helper vs s ks]
  where helper [] y z = True
        helper (x:xs) y z = case lookup x y of
                                 Nothing -> False
                                 Just t  ->
                                   let (vs, b) = (viewAVars t, viewABody t) in
                                   case runKinding t ks of
                                             Left err -> False
                                             Right k | isTerm k && varOrd vs b -> 
                                               helper xs y z
                                                     | otherwise -> False
                                               

boundVars :: [Name] -> Exp -> [Name]
boundVars vs (Const x) = []
boundVars vs (Var x) = if x `elem` vs then [x] else []
boundVars vs (PApp t1 t2) = boundVars vs t1 ++ boundVars vs t2
varOrd :: [Name] -> Exp -> Bool
varOrd vs t = vs == boundVars vs t

kenv = [("Z", Star), ("S", KArrow Star Star)]
t1 = PApp (Var "p") (PApp (PApp (Var "d") (Const "Z")) (Const "Z"))
t2 = PApp (Var "p1") (PApp (PApp (Var "d1") (Const "Z")) (PApp (Const "S") (Const "Z")))
-- hmatch :: MonadPlus m => KSubst -> Exp -> Exp -> StateT Int m [Subst]
-- test1 :: [[Subst]]

a1 = evalState (hmatch kenv t1 t2) 0
a2 = wellKind (free t1) kenv a1
test1 = sep $ map (\ x -> text "[" <+> disp x <+> text "]") $ a1
test2 = length a1
test3 = sep $ map (\ x -> text "[" <+> disp x <+> text "]") $ a2
test4 = length a2

