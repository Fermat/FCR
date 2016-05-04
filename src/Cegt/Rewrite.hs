module Cegt.Rewrite where
import Cegt.PrettyPrinting
import Cegt.Syntax
import Control.Monad
import Data.List
import Data.Tree
import Text.PrettyPrint
import Control.Monad.State
import Control.Monad.Reader

type Subst = [(Name, Exp)]
type Pos = [Int] -- a sequence of 0 and 1, 0 indicates first argument for App

type RedTree = Tree (Pos, Name, Exp)

dispTree :: Tree (Pos, Name, Exp) -> Tree String
dispTree (Node (p, n, e) xs) =
  Node ("["++(concat $ map show p)++"]" ++", " ++ n ++ ", " ++ (show $ disp e)) $ map dispTree xs

reduce :: [(Name, Exp)] -> (Pos, Name, Exp) -> Int -> RedTree
reduce env node n | n == 0 = Node node []
reduce env (p, k, e) n | n > 0 = Node (p,k,e) (map (\ x -> reduce env x (n-1)) $ reduceOne e env)

reduceOne :: Exp -> [(Name, Exp)] -> [(Pos, Name, Exp)]
reduceOne e env = [(p, n, replace e p r') | ((p, r), l) <- getReductions e env, (n, r') <- l]

replace :: Exp -> Pos -> Exp -> Exp
replace e [] r = r
replace (App t1 t2) (x:xs) r | x ==1 = App t1 (replace t2 xs r)
replace (App t1 t2) (x:xs) r | x ==0 = App (replace t1 xs r) t2
replace (Lambda y t2) (x:xs) r | x == 1 = Lambda y (replace t2 xs r) 

getReductions :: Exp -> [(Name, Exp)] -> [((Pos, Exp), [(Name, Exp)])]
getReductions x env = [((p, e), r) | (p, e) <- getSubterms x, let r = allMatches e env, r /= [] ]

getSubterms :: Exp -> [(Pos, Exp)]
getSubterms x = runReader (subterms x) []

subterms :: Exp -> Reader Pos [(Pos, Exp)]
subterms (Var x) = do p <- ask
                      return [(p, Var x)]
subterms (Const x) = do p <- ask
                        return [(p, Const x)]

subterms (App t1 t2) = do l1 <- local (\r -> r++[0]) (subterms t1)
                          l2 <- local (\r -> r++[1]) (subterms t2)
                          p <- ask
                          return ((p, (App t1 t2)):(l1++l2))

data Trace = Trace [(Pos, Subst, Name, Exp)]
instance Disp Trace where
  disp (Trace ((_, _, _, e):decl)) = vcat (disp e : (map (\ (_, _, n, exp) -> text "-" <> disp n <> text "->" <+> disp exp) decl))


stepsInner :: [(Name, Exp)] -> Exp -> Int -> State Trace ()
stepsInner env e n | n == 0 = return ()
stepsInner env e n | n > 0 = case stepInner env e of
                                Nothing -> return ()
                                Just (p, sub, k, e') ->
                                  do modify (\ (Trace s) -> Trace (s ++ [(p, sub, k,e')]))
                                     stepsInner env e' (n-1)

stepInner :: [(Name, Exp)] -> Exp -> (Maybe (Pos, Subst, Name, Exp))
stepInner env e = case e of
                    App a b ->
                      case (step env a) of
                        Nothing -> case step env b of
                                      Nothing -> case firstMatch e env of
                                                   Just (k, e', s) -> Just ([], s, k, e')
                                                   _ -> Nothing
                                      Just (p, s, n, b') -> Just (1:p, s, n, App a b')
                        Just (p, s, n, a') -> Just (0:p, s, n, App a' b)
                    _ -> Nothing


getTrace env e n = execState (steps env e n) (Trace [([],[],"", e)])
getTrace' env e n = execState (stepsInner env e n) (Trace [([],[],"", e)])

steps :: [(Name, Exp)] -> Exp -> Int -> State Trace ()
steps env e n | n == 0 = return ()
steps env e n | n > 0 = case step env e of
                            Nothing -> return ()
                            Just (p, sub, k, e') ->
                              do modify (\ (Trace s) -> Trace (s ++ [(p,sub, k,e')]))
                                 steps env e' (n-1)

step :: [(Name, Exp)] -> Exp -> (Maybe (Pos, Subst, Name, Exp))
step env e = case firstMatch e env of
                    Nothing -> case e of
                                   App a b ->
                                     case (step env a) of
                                       Nothing -> case step env b of
                                                    Nothing -> Nothing
                                                    Just (p, s, n, b') ->
                                                      Just (1:p, s, n, App a b')
                                       Just (p, s, n, a') -> Just (0:p, s, n, App a' b)
                                   _ -> Nothing
                    Just (k, e', s) -> Just ([], s, k, e')

firstMatch :: Exp -> [(Name, Exp)] -> Maybe (Name, Exp, Subst)
firstMatch  x [] = Nothing
firstMatch  x ((k, Arrow l r):ys) = 
         case match l x of
           Nothing -> firstMatch x ys
           Just s -> Just $ (k, applyE s r, s)


allMatches :: Exp -> [(Name, Exp)] -> [(Name, Exp)]
allMatches x env = [ (k, applyE s r)  | (k, Arrow l r) <- env, s <- match l x]



match (Var s) t1 = return [(s, t1)]
match (App t1 t2) (App t1' t2') = do
  s1 <- match t1 t1'
  s2 <- match t2 t2'
  merge s1 s2
match (Const s) (Const t) | s == t = return []
match _ _ = mzero

merge :: MonadPlus m => Subst -> Subst -> m Subst
merge s1 s2 = if agree then return $ nub (s1 ++ s2) else mzero
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

applyE subs (Lambda y f) =
 let subs' = filter (\(x, _) -> not (x == y)) subs in
 Lambda y (applyE subs' f)

applyE subs (App f1 f2) =
  let a1 = applyE subs f1
      a2 = applyE subs f2 in
  App a1 a2

applyE subs (Imply b h) =
  let a1 = applyE subs h
      a2 = applyE subs b in
  Imply a2 a1
        

