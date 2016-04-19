module Cegt.Rewrite where

import Cegt.Syntax
import Control.Monad
import Data.List
import Control.Monad.State
import Control.Monad.Reader

data Trace = Branch Name Exp [Trace] deriving (Show, Eq, Ord)

-- reduce :: Exp -> StateT Trace (Reader [(Name, Exp)]) Exp
-- reduce e = do rules <- ask
--               let matches = [  map (\(Arrow x y) -> ) rules]
              
steps :: [(Name, Exp)] -> Exp -> Int -> Exp
steps env e n | n == 0 = e
steps env e n | n > 0 = case firstMatch e env of
                           Nothing -> case e of
                             App a b -> App (steps env a n) (steps env b n)
                             _ -> e
                           Just (k, e') -> steps env e' (n-1)


firstMatch  x [] = Nothing
firstMatch  x ((k, Arrow l r):ys) = 
         case match l x of
           Nothing -> firstMatch x ys
           Just s -> Just $ (k, applyE s r)

                                    
matchRule l n e =  match l e >>= \ s -> return (n, s)





type Subst = [(Name, Exp)]

match (Var s) t1 = return [(s, t1)]
match (App t1 t2) (App t1' t2') = do
  s1 <- match t1 t1'
  s2 <- match t2 t2'
  merge s1 s2
match (Const s) (Const t) | s == t = return []
match _ _ = mzero

merge :: MonadPlus m => Subst -> Subst -> m Subst
merge s1 s2 = if agree then return $ s1 ++ s2 else mzero
  where agree = all (\ x -> applyE s1 (Var x) == applyE s2 (Var x)) (map fst s1 `intersect` map fst s2) 


applyE :: Subst -> Exp -> Exp
applyE subs a@(Const x) = a
applyE subs (Var x) =
  case lookup x subs of
    Just x1 -> x1
    Nothing -> Var x

applyE subs (Arrow f1 f2) =
  let a1 = applyE subs f1
      a2 = applyE subs f2 in
  Arrow a1 a2

applyE subs (Forall y f) =
 let subs' = filter (\(x, _) -> not (x == y)) subs in
 Forall y (applyE subs' f)

applyE subs (App f1 f2) =
  let a1 = applyE subs f1
      a2 = applyE subs f2 in
  App a1 a2

applyE subs (Imply b h) =
  let a1 = applyE subs h
      a2 = applyE subs b in
  Imply a2 a1
        

