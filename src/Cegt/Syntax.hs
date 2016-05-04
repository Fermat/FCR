module Cegt.Syntax where

-- import Control.Monad.State.Lazy
-- import Control.Monad.Reader

import Data.Char
import qualified Data.Set as S
import Data.List hiding (partition)
import Text.Parsec
import Text.Parsec.Pos

type Name = String

-- merge prog, kind, type into one syntactic category.
data Exp = Var Name
          | Star 
          | Const Name
          | App Exp Exp 
          | Lambda Name Exp 
          | Imply Exp Exp
          | Arrow Exp Exp
          | Forall Name Exp
          deriving (Show, Eq, Ord)
type Module = [(Name, Exp)] 

toFormula :: [(Name, Exp)] -> [(Name, Exp)]
toFormula env = map (\(n,e)-> (n, helper e)) env
   where helper a@(Arrow t t') =
           let vars = "p" : free a in
           foldr (\ z x -> Forall z x) (Imply (App (Var "p") t') (App (Var "p") t)) vars


data Tactic = Coind Name
          | Intros [(Name, Exp)]
          | Apply Name [Exp]
          | Resolve Name
          deriving (Show, Eq, Ord)

free = nub . freeVar 
freeVar :: Exp -> [Name]
freeVar (Var x) =  [x]
freeVar (Const x) = []
freeVar (Arrow f1 f2) = (freeVar f1) ++ (freeVar f2)
freeVar (App f1 f2) = (freeVar f1) ++ (freeVar f2)
freeVar (Forall x f) = delete x (freeVar f)
freeVar (Imply b h) = freeVar b ++ freeVar h

flatten :: Exp -> [Exp]
flatten (App f1 f2) = flatten f1 ++ [f2]
flatten a = [a]

-- freeKVar :: Exp -> S.Set Name
-- freeKVar Star = S.empty
-- freeKVar (KVar x) = S.insert x S.empty
-- freeKVar (KArrow f1 f2) = (freeKVar f1) `S.union` (freeKVar f2)


-- note that this is a naive version of getting
-- free variable, since fv  will consider data
-- type constructors and program definitions as
-- free variables. So one would need to aware
-- of this when using fv.
-- type Subst = [(Name, Exp)]        

-- fv :: Exp -> S.Set Name
-- fv (Con x) = S.empty
-- fv (EVar x) = S.insert x S.empty
-- fv (App f1 f2) = fv f1 `S.union` fv f2
-- fv (Lambda x s) = S.delete x (fv s)
-- fv (Let bs p) =
--   let binds = S.fromList $ map fst bs
--       tvars = S.unions $ map fv $ map snd bs
--       pvar = fv p in
--   S.difference (S.union pvar tvars) binds

-- fv (Match p cases) =
--   S.unions (map fvCase cases) `S.union` fv p
--     where fvCase (c, params, t) =
--             S.difference (fv t) (S.fromList params)
            
-- fv (Pos _ t) = fv t

-- -- applyQ currently only used at freshInst

-- applyQ :: Subst -> QType -> QType
-- applyQ subs (DArrow fs f) =
--   let fs' = map (applyE subs) fs
--       f' = applyE subs f in
--   DArrow fs' f'
      
-- applyE :: Subst -> Exp -> Exp
-- applyE subs a@(Con x) = a
-- applyE subs (EVar x) =
--   case lookup x subs of
--     Just x1 -> x1
--     Nothing -> EVar x

-- applyE subs (Arrow f1 f2) =
--   let a1 = applyE subs f1
--       a2 = applyE subs f2 in
--   Arrow a1 a2

-- applyE subs (Forall y f) =
--  let subs' = filter (\(x, _) -> not (x == y)) subs in
--  Forall y (applyE subs' f)

-- applyE subs (FApp f1 f2) =
--   let a1 = applyE subs f1
--       a2 = applyE subs f2 in
--   FApp a1 a2

-- applyE subs (Imply bs h) =
--   let a1 = applyE subs h
--       a2 = map (applyE subs) bs in
--   Imply a2 a1
        
-- -- substituting term
-- applyE subs (App a b) = App (applyE subs a) (applyE subs b)

-- applyE subs (Lambda x p) = Lambda x (applyE subs p)

-- applyE subs (Match p branches) =
--   Match (applyE subs p) $ map (helper subs) branches
--   where helper subs (c, xs, p) = (c, xs, applyE subs p)

-- applyE subs (Let xs p) =
--   Let (map (helper subs) xs) (applyE subs p)
--   where helper subs (x, def) = (x, applyE subs def)

-- applyE subs (Pos _ p) = applyE subs p

-- firstline (Inst a xs) = Inst a [head xs]

-- apply :: Exp -> Name -> Exp -> Exp
-- apply a x (Con t) = Con t
-- apply a x (EVar t) = if x == t then a else (EVar t)
-- apply a x (App t1 t2) = App (apply a x t1) (apply a x t2)
-- apply a x t1@(Lambda y t) =
--   if x == y then t1
--   else Lambda y (apply a x t)
-- apply a x (Match t branches) = Match (apply a x t) $ map (helper a x) branches
--  where helper b y (c, args, p) = if y `elem` args then (c, args, p) else (c, args, apply b y p)
-- apply a x (Let branches p) =
--   let binds = map fst branches in
--   if x `elem` binds then (Let branches p)
--   else Let (map (\ (e,d) -> (e, apply a x d)) branches) (apply a x p)
-- apply a x t1@(Forall y t) =
--   if x == y then t1
--   else Forall y (apply a x t)

-- apply a x (FApp p1 p2) = FApp (apply a x p1) (apply a x p2)
-- apply a x (Imply bds h) = Imply (map (apply a x) bds) (apply a x h)
-- apply a x (Pos _ p) = apply a x p       

-- applyK :: [(Name, Exp)] -> Exp -> Exp
-- applyK _ Star = Star

-- applyK subs (KVar x) =
--   case lookup x subs of
--     Just x1 -> x1
--     Nothing -> KVar x

-- applyK subs (KArrow f1 f2) =
--   let a1 = applyK subs f1
--       a2 = applyK subs f2 in
--   KArrow a1 a2

-- flatApp (Pos _ p) = flatApp p
-- flatApp (App t1 t2) = flatApp t1 ++ [t2]
-- flatApp (FApp t1 t2) = flatApp t1 ++ [t2]
-- flatApp t = [t]

-- makeName name = do
--   m <- get
--   modify (+1)
--   return $ name ++ show m

-- inst (Forall x t) = do
--    newVar <- makeName "x"
--    t' <- inst t
--    return $ apply (EVar newVar) x t'
-- inst a = return a   

-- quantify t =
--   let fs = S.toList $ freeVar t in
--   foldr (\ z x -> Forall z x) t fs
  
