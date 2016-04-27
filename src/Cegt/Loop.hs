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

partial (Trace (t:tr)) = Lambda "`a" $ construct tr
construct ::  [(Pos, Subst, Name, Exp)] -> Exp
construct [] = (Var "`a")
construct ((p, s, n, e):xs) =
  let codomain = map snd s
      cxt = Lambda "`h" $ replace e p (Var "`h")
      pf = foldl' (\ z x -> App z x) (App (Const n) cxt) codomain
  in App pf (construct xs)


