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

-- cycleProof :: ([Name], [Name]) -> [(Pos, Subst, Name, Exp)] -> [(Name, Exp)]
-- cycleProof (pre, cyc) env e = resolve pre env e

top :: [(Pos, Subst, Name, Exp)] -> (Exp, Exp)
top prefix = let pf = construct prefix
                 (_,_,_,ch) = last prefix in
             (applyE [("`a", Var "d")] pf, ch)

loop :: Exp ->  [(Pos, Subst, Name, Exp)] -> Maybe Exp
loop ch tr = let (_,_,_,e') = last tr
                 pf = construct tr 
                 cyc = [(p, s) | (p, t) <- getSubterms e', s <- match ch t]
              in case cyc of
                   [] -> Nothing
                   (p,s):[] -> let cxt = Lambda "`h" $ replace e' p (Var "`h")
                                   codomain = map snd s
                                   r = foldl' (\ z x -> App z x) (App (Var "d") cxt) codomain
                               in Just $ applyE [("`a", r)] pf 
                 
                


partial (Trace (t:tr)) = Lambda "`a" $ construct tr
construct :: [(Pos, Subst, Name, Exp)] -> Exp
construct [] = (Var "`a")
construct ((p, s, n, e):xs) =
  let codomain = map snd s
      cxt = Lambda "`h" $ replace e p (Var "`h")
      pf = foldl' (\ z x -> App z x) (App (Const n) cxt) codomain
  in App pf (construct xs)


