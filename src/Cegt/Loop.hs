module Cegt.Loop where
import Cegt.Syntax
import Cegt.Rewrite
import Data.List

constrLoop :: Trace -> [(Name, Exp)]
constrLoop (Trace tr) = let ns = map (\(_, _, a,_)-> a) tr
                            cs = findCycle ns []
                        in cycleProof cs tr

cycleProof :: ([Name], [Name]) -> [(Pos, Subst, Name, Exp)] -> [(Name, Exp)]
cycleProof (_:pre, cyc) ((_,_,_, e):tr) = let a = take (length pre) tr
                                              b = take (length cyc) $ drop (length pre) tr
                                              (prefix, ch) = top e a
                                              cy = loop ch b
                                          in case cy of
                                               Just c -> [("f", prefix), ("d", c)]
                                               Nothing -> []
                                 

-- getList :: Trace -> [Name]
-- getList (Trace ls) = map (\(_, _, a,_)-> a) ls

findCycle :: [Name] -> [Name] -> ([Name], [Name])
findCycle [] pre = (pre, [])
findCycle (y:ys) pre = case findIndex (\x -> x == y) ys of
                          Nothing -> findCycle ys (pre++[y])
                          Just i ->  (pre, y : take i ys)


top :: Exp -> [(Pos, Subst, Name, Exp)] -> (Exp, Exp)
top e [] = (Var "d", e)
top e prefix = let pf = construct prefix
                   (_,_,_,ch) = last prefix in
               (applyE [("`a", Var "d")] pf, ch)

loop :: Exp ->  [(Pos, Subst, Name, Exp)] -> Maybe Exp
loop ch [] = Nothing
loop ch tr = let (_,_,_,e') = last tr
                 pf = construct tr 
                 cyc = [(p, s) | (p, t) <- getSubterms e', s <- match ch t]
              in case cyc of
                   [] -> Nothing
                   (p,s):[] -> let cxt = Abs "`h" $ replace e' p (Var "`h")
                                   codomain = map snd s
                                   r = foldl' (\ z x -> TApp z x) (TApp (Var "d") cxt) codomain
                               in Just $ applyE [("`a", r)] pf 
                 
                


partial (Trace ((_,_,_,t):tr)) = Lambda "`a" (Just t) $ construct tr

construct :: [(Pos, Subst, Name, Exp)] -> Exp
construct [] = (Var "`a")
construct ((p, s, n, e):xs) =
  let codomain = map snd s
      cxt = Abs "`h" $ replace e p (Var "`h")
      pf = foldl' (\ z x -> TApp z x) (TApp (Const n) cxt) codomain
  in App pf (construct xs)


