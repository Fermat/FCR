module Cegt.Typeinference where

import Cegt.Syntax
import Cegt.Interaction
import Cegt.Monad
import Cegt.Rewrite hiding (merge')

import Cegt.PrettyPrinting
import Cegt.Typecheck
import Control.Monad.State
import Text.PrettyPrint
import Data.List
import Data.Char
import Debug.Trace

env2 = [("H", KArrow Star (KArrow Star Star)), ("J", KArrow Star Star), ("G", KArrow Star Star), ("S", KArrow Star Star)]
exp1 = (Lambda "a1" Nothing
        (Lambda "a2" Nothing
         (Lambda "a3" Nothing
          (App (Var "a3")
           (App (Var "a1")
            (App (Var "a2")
             (App (App (App (Var "h")
                        (Lambda "b1" Nothing (App (Var "a1") (App (Var "a2") (Var "b1")))))
                   (Var "a2"))
              (Var "a3"))))))))

f1 = Forall "p'" (Forall "f" (Forall "x" (Forall "z" (Imply (Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (PApp (Var "f") (PApp (Const "S") (Var "x"))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "z"))))) (PApp (Var "p") (PApp (PApp (Var "f") (Var "x")) (Var "y"))))))) (Imply (Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (PApp (Const "H") (Var "x")) (PApp (Const "S") (Var "y")))) (PApp (Var "p") (PApp (PApp (Const "H") (PApp (Const "S") (Var "x"))) (Var "y"))))))) (Imply (Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (Const "J") (Var "y"))) (PApp (Var "p") (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "y")))))))) (PApp (Var "p'") (PApp (PApp (Var "f") (PApp (Const "S") (Var "x"))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "z")))))))))))

initstate1 = [("h", f1, [([], f1, [])])]
man1 = [s | s <- construction "h" env2 initstate1 exp1, success s]

g1 = PApp (Var "p'") (PApp (PApp (Var "f") (PApp (Const "S") (Var "x"))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "z"))))
g1' = PApp (Var "p''") (PApp (PApp (Var "f'") (PApp (Const "S") (Var "x'"))) (PApp (Const "G") (PApp (PApp (Const "H") (Var "x'")) (Var "z'"))))
h1 = PApp (Var "p1") (PApp (Const "G") (PApp (PApp (Const "H") (Var "x2")) (Var "y3")))
man2 = runHMatch env2 h1 g1 
success :: ProofState -> Bool
success (gn,pf,[]) = True
success _ = False

construction :: Name -> KSubst -> [ProofState] -> Exp -> [ProofState]
construction n ks init exp | trace (show ( n) ++ "-- " ++show (disp exp) ++ "\n" ++ show init) False = undefined
construction n ks init (Var v) =
  [s | Just s <- map (\ x -> useF x v) init]

construction n ks init a@(Lambda x Nothing t) =
  let (vars, b) = (map fst $ viewLVars a, viewLBody a)
      new = map (\ x -> intros x vars) init 
  in construction n ks new b

construction n ks init (App (Const k) p2) =
  let next = [s | Just s <- map (\ x -> applyF x k) init]
  in
   if null next then
     do nex <-  map (\x -> applyH ks x k) init
        construction n ks nex p2
   else construction n ks next p2


construction n ks init (App (Var v) p2) | v /= n =
  let next = [s | Just s <- map (\ x -> applyF x v) init]
  in
   if null next then
     do nex <-  map (\x -> applyH ks x v) init
        construction n ks nex p2
   else construction n ks next p2

-- [[state]]
construction n ks init (App (Var v) p2) | v == n =
  do next <-  map (\x -> applyH ks x v) init
     
     construction n ks next p2
--  x App (App y z) q
construction n ks init a@(App p1 p2) = 
  case flatten a of
    (Var v): xs | v == n ->
      do next <- map (\ x -> applyH ks x v) init 
         foldl (\ z x -> construction n ks z x) next xs


-- construction n ks init a@(App p1 p2) =

      
-- smart higher order apply using list of success
applyH :: KSubst -> ProofState -> Name -> [ProofState]
applyH ks init k | trace (show ( init) ++ "--ha " ++show (disp k)) False = undefined
applyH ks (gn, pf, []) k = []
applyH ks (gn, pf, (pos, goal, gamma):res) k = 
  case lookup k gamma of
    Nothing -> []
    Just f -> let (vars, head, body) = separate f
                  fresh = map (\ (v, i) -> v ++ show i ++ "fresh") $ zip vars [1..]
                  renaming = zip vars (map Var fresh)
                  body'' = map (applyE renaming) body
                  head'' = applyE renaming head
                  ss = trace (show head''++ "from rhm") $ runHMatch ks head'' goal -- zip fresh ins
              in do
                sub <- trace (show ss ++ "this is ss")$ ss
                let body' = map normalize $ (map (applyE sub) body'')
                    head' = normalize $ applyE sub head''
                    np = map snd sub  -- ++body'
                    name = case k of
                               n:_ -> if isUpper n then Const k else Var k
                               a -> error "unknow error from apply"
                    contm = foldl' (\ z x -> App z x) (foldl' (\ z x -> TApp z x) name np) body'
                    pf' = replace pf pos contm
                    zeros = makeZeros $ length body'
                    ps = map (\ x -> pos++x++[1]) zeros
                    new = map (\(p, g) -> (p, g, gamma)) $ zip ps body'
                return (gn, pf', new++res)  

-- Second order matching, using Gilles Dowek's terminology in his tutorial.
-- tips: the less number of higher order variable, the less number of
-- possible substitution we get. 
runHMatch ks t1 t2 = let a1 = evalState (hmatch ks t1 t2) 0
                         f1 = free t1
                         -- subs = wellKind f1 ks a1
                     in a1 -- [ s' | s <- subs, let s' = [ (x, n) | (x, n) <- s, x `elem` f1 ]]
                     

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
                               n' = n + arity'
                               fvars = map (\ x -> "h" ++ show x) l
                               bvars = map (\ x -> "b" ++ show x) lb
                               bvars' = map Var bvars
                               args = map (\ c -> (foldl' (\ z x -> PApp z x) (Var c) bvars')) fvars
                               body = foldl' (\ z x -> PApp z x) head args
                               res = foldr (\ x y -> Abs x y) body bvars
                           put n'
                           return res


-- assuming one always rename the bound variable, then we
-- don't need to worry about hmatch on two same term, otherwise we cannot
-- distinguish failure from identity                           
hmatch ::  KSubst -> Exp -> Exp -> State Int [Subst]
-- hmatch ks t1 t2 | trace ("(" ++show (disp t1) ++ " --hmatch " ++show (disp t2)++")") False = undefined
hmatch ks t1 t2 | Left err <- runKinding' t1 ks = error $ show err ++ show ks ++ show t1
hmatch ks t1 t2 | Left err <- runKinding' t2 ks = error $ show err 
hmatch ks t1 t2 | Right (k1, sub1) <- runKinding' t1 ks, Right (k2, sub2) <- runKinding' t2 ks = do
  let t1' = flatten t1
      t2' = flatten t2
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

    (x, y) -> return [] -- error $ show x ++ show y -- (text "err" <+> disp x <+> disp y <+> disp x' <+> disp y')-- 


            
mergeL :: [Subst] -> [Subst]
mergeL l = foldM merge' [] l

merge' :: Subst -> Subst -> [Subst]
merge' s1 s2 = if agree then return $ nubBy (\ (n1, _) (n2, _) -> n1 == n2 ) (combine s1 s2)
               else [] -- error $ "hamerge'" ++ show (disp s1) ++ "mmm" ++ show (disp s2) 
  where agree = 
          all (\ x -> normalize (applyE s1 (Var x)) `alphaEq` normalize (applyE s2 (Var x))) (map fst s1 `intersect` map fst s2) 


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

kenv = [("Z", Star), ("S", KArrow Star Star), ("T", Star)]
t1 = (PApp (PApp (Var "d") (Const "Z")) (Const "Z"))
t1' = (PApp (PApp (Var "d1") (Const "Z")) (Const "Z"))
t2 = (PApp (PApp (Var "d1") (Const "Z")) (PApp (Const "S") (Const "Z")))
t3 = PApp (Const "B") (PApp (Var "l") (PApp (Const "B") (Var "x")))
t4 = PApp (Const "B") (PApp (Var "l1") (PApp (Const "A") (PApp (Const "B") (Var "y"))))
t5 = PApp (PApp (PApp (PApp (Var "g") (Const "T")) (Const "T")) (Const "Z")) (PApp (Var "s") (Const "Z"))
t6 = PApp (PApp (PApp (PApp (Var "g1") (Const "T")) (Const "T")) (PApp (Const "S") (Const "Z")))
     (PApp (Var "s1") (PApp (Var "s1") (Const "Z")))
-- hmatch :: MonadPlus m => KSubst -> Exp -> Exp -> StateT Int m [Subst]
-- test1 :: [[Subst]]


a1 = evalState (hmatch kenv t1 t2) 0
a2 = wellKind (free t1) kenv a1
a3 = runHMatch [("B", KArrow Star Star), ("A", Star)] (PApp (Const "B") (Var "q")) (PApp (Const "B") (Const "A"))
a4 = runHMatch [("A", KArrow Star Star), ("B", KArrow Star Star)] t3 t4
a5 = runHMatch kenv t5 t6
test1 = sep $ map (\ x -> text "[" <+> disp x <+> text "]") $ a1
test2 = length a1
test3 = sep $ map (\ x -> text "[" <+> disp x <+> text "]") $ a4
test4 = length a2

