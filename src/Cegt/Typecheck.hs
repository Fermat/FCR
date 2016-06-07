module Cegt.Typecheck where

import Cegt.Syntax
import Cegt.Monad

import Cegt.PrettyPrinting

import Text.PrettyPrint
import Control.Monad.State.Lazy
import Control.Monad.Reader
import Data.Char
import qualified Data.Set as S
import Data.List hiding (partition)

type KCMonad a = StateT Int (StateT KSubst (ReaderT KSubst (Either Doc))) a  

type KSubst = [(Name, Kind)]

kindList :: [Exp] -> KSubst -> Either Doc [Kind]
kindList ts g = mapM (\ x -> runKinding x g) ts

runKinding :: Exp -> KSubst -> Either Doc Kind
runKinding t g = do (k, sub) <- runKinding' t g
                    return $ ground k
  -- runReaderT (evalStateT (evalStateT (inferKind t) 0) []) g

runKinding' :: Exp -> KSubst -> Either Doc (Kind, KSubst)
runKinding' t g = do
  (k, sub) <- runReaderT (runStateT (evalStateT (inferKind t) 0) []) g 
  return (ground k, sub)
  
ground :: Kind -> Kind
ground (KVar x) = Star
ground (KArrow k1 k2) = KArrow (ground k1) (ground k2)
ground Star = Star
ground Formula = Formula

inferKind :: Exp -> KCMonad Kind
inferKind (Const x) | isUpper (head x) = do
  genv <- ask
  case lookup x genv of
    Just k -> return k
    Nothing -> lift $ lift $ lift $ Left $ text "Kinding error: " <+> text "undefine type constructor:" <+> disp x

                    | otherwise  = do
  env <- lift get
  case lookup x env of
    Nothing -> do
      ki <- makeName "k"
      let kind = KVar ki
      lift $ modify (\ e -> (x, kind): e)
      return kind
    Just k -> return k  
  
inferKind (Var x) = do
  env <- lift get
  case lookup x env of
    Nothing -> do
      ki <- makeName "k"
      let kind = KVar ki
      lift $ modify (\ e -> (x, kind): e)
      return kind
    Just k -> return k  
  
inferKind (PApp f1 f2) = do
  k1 <- inferKind f1
  k2 <- inferKind f2
  unificationK k2 Star
  k <- makeName "k"
  unificationK k1 $ KArrow Star (KVar k) 
  return (KVar k) 

inferKind (Abs x t) = do
  lift $ modify (\ e -> (x, Star): e)
  let vars = free t
      l = intersect vars [x]
  case l of
    a:b:_ -> lift $ lift $ lift $ Left $ text "multiple use of variable " <+> text x 
    a:[] -> do k <- inferKind t
               let k' = ground k
               case isTerm k' of
                 True -> return $ KArrow Star k
                 False -> lift $ lift $ lift $ Left $ text "the body " <+> (disp t) <+> text " is ill-kind"
    [] -> lift $ lift $ lift $ Left $ text "no use of variable " <+> text x
      
inferKind (Imply f1 f2) = do
  k1 <- inferKind f1
  k2 <- inferKind f2
  case (isForm f1, isForm f2) of
    (True, True) -> do 
      unificationK k1 Formula
      unificationK k2 Formula
      return Formula
    (True, False) -> do 
      unificationK k1 Formula
      unificationK k2 Star
      return Formula
    (False, True) -> do 
      unificationK k1 Star
      unificationK k2 Formula
      return Formula
    (False, False) -> do 
      unificationK k1 Star
      unificationK k2 Star
      return Formula

inferKind (Forall x f) = do
  k <- inferKind f
  case isForm f of
    True -> do unificationK k Formula
               return Formula
    False -> do unificationK k Star
                return Formula

inferKind a = error $ show a ++ "from function inferKind"
isForm (Imply x y) = True
isForm (Forall x y) = True
isForm (App _ _) = False
isForm _ = False

isTerm (Star) = True
isTerm (KArrow Star t) = isTerm t
isTerm _ = False

makeName name = do
  m <- get
  modify (+1)
  return $ name ++ show m

combineK :: KSubst -> KSubst -> KSubst
combineK s2 s1 =
   s2 ++ [(v, applyK s2 t) | (v, t) <- s1] 

unifyK :: Kind -> Kind -> KCMonad KSubst
unifyK (KArrow t1 t2) (KArrow a1 a2) = do
  s1 <- unifyK t1 Star
  s11 <- unifyK a1 Star
  s2 <- unifyK (applyK s11 (applyK s1 t2)) (applyK s11 (applyK s1 a2))
  return $ combineK (combineK s2 s1) s11

unifyK (KVar tn) t =
  varBindK tn t
unifyK t (KVar tn) = varBindK tn t

unifyK Star Star = return []

unifyK Formula Formula = return []

unifyK t t' = lift $ lift $ lift $ Left $ text "Unification failure during Kinding: "
              <+> text "trying to unify" <+> disp t <+> text "with" <+> disp t'

varBindK x t | t == KVar x = return []
             | x `S.member` freeKVar t =
               lift $ lift $ lift $ Left $ text "Occur-Check failure during Kinding: "
                <+> text "trying to unify" <+> disp x <+> text "with" <+> disp t
             | otherwise = return [(x, t)]

unificationK :: Kind -> Kind -> KCMonad ()
unificationK t1 t2 = do
  subs <- lift get
  new <- unifyK (applyK subs t1) (applyK subs t2)
  lift $ put $ combineK new subs

-- applyK :: [(Name, Kind)] -> Kind -> Kind
-- applyK _ Star = Star
-- applyK _ Formula = Formula
-- applyK subs (KVar x) =
--   case lookup x subs of
--     Just x1 -> x1
--     Nothing -> KVar x

-- applyK subs (KArrow Star f2) =
--   let a2 = applyK subs f2 in
--   KArrow Star a2


type PCMonad a = (ReaderT [(Name, Exp)] (ReaderT KSubst (Either Doc))) a

-- use current axioms and lemmas to check more lemma 
runProofCheck :: Name -> Exp -> Exp -> Env -> Either Doc ()
runProofCheck n t f env = do
  let ev = (n, f) : (axioms env ++ (map (\ (x, (_, f)) -> (x, f)) $ lemmas env))
      ks = kinds env
--  error $ show (disp t)
  case runReaderT (runReaderT (proofCheck t) ev) ks of
    Left err -> Left err
    Right f' -> if f' `alphaEq` f then return ()
                else Left $ sep [text "proof checking error", text "expected type:" <+> disp f,
                          text "actual type:", disp f']
  
-- check a type exp is either of kind * or o
kindable :: Exp -> KSubst -> PCMonad ()
kindable t ks = case runKinding t ks of
                   Left err -> lift $ lift $ Left $ text "ill-kinded type: " <+> disp t
                   Right a -> case a of
                                 Formula -> return ()
                                 Star -> return ()
                                 e -> lift $ lift $ Left ((text "ill-kinded type " <+> disp t) $$
                                                          nest 2 (text "expected: o or *" <+>
                                                                  text "actual kind:" <+> disp e)) 


proofCheck :: Exp -> PCMonad Exp
proofCheck (Var x) = do env <- ask
                        case lookup x env of
                             Nothing -> lift $ lift $ Left 
                                        $ text "proof checking error: undefined variable" 
                                        <+> text x
                             Just f -> do
                               ks <- lift ask 
                               kindable f ks
                               return f

proofCheck (Const x) =
                       do env <- ask
                          case lookup x env of
                              Nothing -> lift $ lift $ Left 
                                         $ text "proof checking error: unknown constant" 
                                         <+> text x
                              Just f -> do
                               ks <- lift ask 
                               kindable f ks
                               return f
                     
proofCheck (App e1 e2)  = do f1 <- proofCheck e1 
                             f2 <- proofCheck e2
                             case f1 of
                                Imply a1 a2 -> 
                                    if a1 `alphaEq` f2
                                    then return a2
                                    else lift $ lift $ Left 
                                         ((text "proof checking error at application"
                                         <+> disp (App e1 e2)) $$ (nest 2 $ text "relevant types:" <+> disp f1)
                                         $$ (nest 2 $ disp f2))
                                b ->  lift $ lift $ Left 
                                      ((text "proof checking error at application"
                                        <+> disp (App e1 e2)) $$ (nest 2 $ text "relevant types:" <+> disp f1)
                                       $$ (nest 2 $ disp f2))
                                 

proofCheck (Lambda x (Just t1) t) = do t' <- local (\ y -> (x, t1) : y) (proofCheck t)
                                       return $ Imply t1 t'

proofCheck (Lambda x Nothing t) = do
  f <- proofCheck t
  e <- ask
  if isFree x e
    then lift $ lift $ Left $
         sep [text "proof checking error", text "generalized variable" <+> disp x, text "appears in the assumptions", text "when checking the proof", nest 2 $ disp (Lambda x Nothing t), text "current assumption", nest 2 $ disp e ]
    else do
    ks <- lift ask
    (k, sub) <- lift $ lift $ runKinding' (Forall x f) ks
    case lookup x sub of
      Nothing -> lift $ lift $ Left $
         sep [text "proof checking error", text "vacuous abstraction on variable" <+> disp x]
      Just l -> if isTerm $ ground l then return $ (Forall x f)
                else lift $ lift $ Left $
                     sep [text "proof checking error", text "ill-kinded variable" <+> disp x,
                          text "with kind", disp l]


proofCheck (TApp e1 e2)  = do f1 <- proofCheck e1
                              ks <- lift ask
                              k <- lift $ lift $ runKinding e2 ks
                              if isTerm k then 
                                case f1 of
                                  Forall x a2 -> 
                                     do let res = normalize $ runSubst e2 (Var x) a2
                                        kindable res ks   
                                        return res    
                                   
                                  b -> lift $ lift $ Left $
                                        (text "proof checking error on"
                                         <+> disp e1) $$ (nest 2 $ text "unexpected type:" <+> disp b)
                                else  lift $ lift $ Left $
                                      (text "kinding checking error on"
                                       <+> disp e2) $$ (nest 2 $ text "unexpected kind:" <+> disp k)
                                       

proofCheck a = error $ show (disp a <+> text "from proofCheck function") 
isFree :: Name -> [(Name, Exp)] -> Bool
isFree x m = let a = (filter (\ y ->  x `elem` (free (snd y))) m) in
  if not (null a) then error $ show a else False

-- test1 = free $ Forall "p" (Forall "x" (Forall "y" (Imply (PApp (Var "p") (PApp (Const "J") (Var "y"))) (PApp (Var "p") (PApp (Const "G") (PApp (PApp (Const "H") (Var "x")) (Var "y")))))))





runHMatch ks t1 t2 = let a1 = evalState (hmatch ks t1 t2) 0
                         f1 = free t1
                         subs = wellKind f1 ks a1
                     in [ s' | s <- subs, let s' = [ (x, n) | (x, n) <- s, x `elem` f1 ]]
                     

-- generating projection based on kind
genProj :: Kind -> [Exp]
genProj k = let ks = flattenK k
                l = (length ks) - 1
            in if l == 0 then []
               else let vars = map (\ y -> "x"++ show y ++ "'") $ take l [1..]
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
                               fvars = map (\ x -> "h" ++ show x ++ "'") l
                               bvars = map (\ x -> "m" ++ show x ++ "'") lb
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



hunif ::  KSubst -> [(Exp, Exp)] -> State Int [Subst]
-- hunif ks t1 t2 | trace ("(" ++show (disp t1) ++ " --hunif " ++show (disp t2)++")") False = undefined
hunif ks ((t1, t2):res) | Left err <- runKinding' t1 ks = error $ show err ++ show ks ++ show t1
hunif ks ((t1, t2):res) | Left err <- runKinding' t2 ks = error $ show err 
hunif ks ((t1, t2):res) | Right (k1, sub1) <- runKinding' t1 ks, Right (k2, sub2) <- runKinding' t2 ks = do
  let t1' = flatten t1
      t2' = flatten t2
  case (t1', t2') of
    ((Const x):xs, (Const y):ys) ->
      if x == y then
        hunif ks ((zip xs ys):res)
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
                  new2 = normalize $ runSubst imi (Var x) t2
                  imiAndProj = (renew, new2) : map (\ x -> (x, new2)) xs
                  oldsubst = [(x, imi)]: map (\ y -> [(x,y)]) pjs
              put n'
              bs <- hunif ks imiAndProj
              let
                ps = zip bs oldsubst
                res = map (\ (x, y) -> map (\z -> concat $ merge' z y) x) ps
              return (concat res)
    ((Const y):xs, (Var x):ys) ->
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
