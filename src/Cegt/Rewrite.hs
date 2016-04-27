module Cegt.Rewrite where
import Cegt.PrettyPrinting
import Cegt.Syntax
import Control.Monad
import Data.List
import Data.Tree
import Text.PrettyPrint
import Control.Monad.State
import Control.Monad.Reader

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

data Trace = Trace [(Pos, Name, Exp)]
instance Disp Trace where
  disp (Trace ((_, _, e):decl)) = vcat (disp e : (map (\ (n, exp) -> text "-" <> disp n <> text "->" <+> disp exp) decl))


stepsInner :: [(Name, Exp)] -> Exp -> Int -> State Trace ()
stepsInner env e n | n == 0 = return ()
stepsInner env e n | n > 0 = case stepInner env e of
                                Nothing -> return ()
                                Just (k, e') -> do modify (\ (Trace s) -> Trace (s ++ [(k,e')]))
                                                   stepsInner env e' (n-1)

stepInner :: [(Name, Exp)] -> Exp -> (Maybe (Name, Exp))
stepInner env e = case e of
                    App a b ->
                      case (step env a) of
                        Nothing -> case step env b of
                                      Nothing -> case firstMatch e env of
                                                   Just (k, e') -> Just (k, e')
                                                   _ -> Nothing
                                      Just (n, b') -> Just (n, App a b')
                        Just (n, a') -> Just (n, App a' b)
                    _ -> Nothing


getTrace env e n = execState (steps env e n) (Trace [("", e)])
getTrace' env e n = execState (stepsInner env e n) (Trace [("", e)])
steps :: [(Name, Exp)] -> Exp -> Int -> State Trace ()
steps env e n | n == 0 = return ()
steps env e n | n > 0 = case step env e of
                            Nothing -> return ()
                            Just (k, e') -> do modify (\ (Trace s) -> Trace (s ++ [(k,e')]))
                                               steps env e' (n-1)

                                               

step :: [(Name, Exp)] -> Exp -> (Maybe (Name, Exp))
step env e = case firstMatch e env of
                    Nothing -> case e of
                                   App a b ->
                                     case (step env a) of
                                       Nothing -> case step env b of
                                                    Nothing -> Nothing
                                                    Just (n, b') -> Just (n, App a b')
                                       Just (n, a') -> Just (n, App a' b)
                                   _ -> Nothing
                    Just (k, e') -> Just (k, e')

firstMatch :: Exp -> [(Name, Exp)] -> Maybe (Name, Exp)
firstMatch  x [] = Nothing
firstMatch  x ((k, Arrow l r):ys) = 
         case match l x of
           Nothing -> firstMatch x ys
           Just s -> Just $ (k, applyE s r)


allMatches :: Exp -> [(Name, Exp)] -> [(Name, Exp)]
allMatches x env = [ (k, applyE s r)  | (k, Arrow l r) <- env, s <- match l x]

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
        

