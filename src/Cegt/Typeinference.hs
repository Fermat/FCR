module Cegt.Typeinference where

import Cegt.Syntax
import Cegt.Monad

import Cegt.PrettyPrinting
import Cegt.Typecheck

import Text.PrettyPrint



genType :: Kind -> [Exp]
genType k = let ks = flattenK k
                l = (length ks) - 1
            in if l == 0 then []
               else let vars = map (\ y -> "x"++ show y) $ take l [1..]
                        ts = map (\ z -> foldr (\ x y -> Abs x y) (Var z) vars) vars
                    in ts
                    
  
                

{-
hmatch :: KSubst -> Exp -> Exp -> [Subst]
hmatch ks t1 t2 =
  let t1' = flatten t1
      t2' = flatten t2'
      (k1, sub1) = runKinding' t1 ks
  in
  case (t1', t2') of
    ((Const x):xs, (Const y):ys) ->
      if x == y then
        concat $ map hmatch (zip xs ys)
      else Nothing
    ((Var x):xs, (Const y):ys) -> 
-}           
