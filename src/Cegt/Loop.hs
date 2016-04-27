module Cegt.Loop where
import Cegt.Syntax
import Cegt.Rewrite
import Data.List

getList :: Trace -> [Name]
getList (Trace ls) = map (\(_, _, a,_)-> a) ls

findCycle :: [Name] -> [Name] -> ([Name], [Name])
findCycle [] pre = (pre, [])
findCycle (y:ys) pre = case findIndex (\x -> x == y) ys of
                          Nothing -> findCycle ys (pre++[y])
                          Just i ->  (pre, y : take i ys)

-- cycleProof :: ([Name], [Name]) -> [(Name, Exp)] -> Exp -> [(Name, Exp)]
-- cycleProof (pre, cyc) env e = resolve pre env e

construct ::  [(Pos, Subst, Name, Exp)] -> Exp
construct [] = (Var "partial")
construct ((p, s, n, e):xs) =
  let codomain = map snd s
      cxt = Lambda "hole" $ replace e p (Var "hole")
      pf = foldl' (\ z x -> App z x) (App (Const n) cxt) codomain
  in Lambda "partial" $ App pf (construct xs)


