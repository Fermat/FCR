module Cegt.Syntax where

import Control.Monad.State.Lazy
import Control.Monad.Reader

import Data.Char
import qualified Data.Set as S
import Data.List hiding (partition)


type Name = String

-- evidence, type
data Exp = Var Name
          | Const Name
          | App Exp Exp
          | TApp Exp Exp
          | PApp Exp Exp
          | Lambda Name (Maybe Exp) Exp
          | Abs Name Exp
          | Imply Exp Exp
          | Arrow Exp Exp
          | Forall Name Exp
          deriving (Show, Eq, Ord)

data Kind = Formula
          | Star
          | KVar Name
          | KArrow Kind Kind
          deriving (Show, Eq)

-- nameless for the type
data Nameless = V Int
              | C Name
              | IMP Nameless Nameless
              | ALL Nameless
              | AP Nameless Nameless
              | LAM Nameless
             deriving (Show, Eq)

-- [Exp] for Apply and Use are all types
data Tactic = Apply Name [Exp]
            | Coind
            | Use Name [Exp]
            | Intros [Name]
            deriving (Show)
                     
data Module = Mod {decls :: [(Name, Exp)] , prfs :: [((Name, Exp), [Tactic])]}
            deriving (Show)
                     
toFormula :: [(Name, Exp)] -> [(Name, Exp)]
toFormula env = map (\(n,e)-> (n, helper e)) env
   where helper a@(Arrow t t') =
           let vars = "p" : free a in
           foldr (\ z x -> Forall z x) (Imply (App (Var "p") t') (App (Var "p") t)) vars


-- free vars of exp
free = S.toList . freeVar 
-- freeVar :: Exp -> [Name]
freeVar (Var x) =  S.insert x S.empty
freeVar (Const x) = S.empty
freeVar (Arrow f1 f2) = (freeVar f1) `S.union` (freeVar f2)
freeVar (App f1 f2) = (freeVar f1) `S.union` (freeVar f2)
freeVar (TApp f1 f2) = (freeVar f1) `S.union` (freeVar f2)
freeVar (PApp f1 f2) = (freeVar f1) `S.union` (freeVar f2)
freeVar (Forall x f) = S.delete x (freeVar f)
freeVar (Lambda x (Just f1) f) =
  S.delete x $ freeVar f `S.union` freeVar f1
freeVar (Lambda x Nothing f) =
  S.delete x $ freeVar f   
freeVar (Abs x f) = S.delete x (freeVar f)
freeVar (Imply b h) = freeVar b `S.union` freeVar h

freeKVar :: Kind -> S.Set Name
freeKVar Star = S.empty
freeKVar (KVar x) = S.insert x S.empty
freeKVar (KArrow f1 f2) = (freeKVar f1) `S.union` (freeKVar f2)

-- flatten of type
flatten :: Exp -> [Exp]
flatten (PApp f1 f2) = flatten f1 ++ [f2]
flatten a = [a]

flattenK :: Kind -> [Kind]
flattenK (KArrow f1 f2) =  f1 : flattenK f2
flattenK a = [a]


type BindCxt a = Reader [(Name, Int)] a

-- debruijn representation of type 
debruijn :: Exp -> BindCxt Nameless
debruijn (Const x) = return $ C x
debruijn (Var x) = do 
  Just n <- asks (lookup x) 
  return $ V n

debruijn (Forall x f) = do 
  a <- local (((x,0):) . plus1) $ debruijn f 
  return $ ALL a
  
debruijn (Imply f1 f2) = do
  a1 <- debruijn f1
  a2 <- debruijn f2
  return $ IMP a1 a2

debruijn (PApp b1 b2) = do
  a <- debruijn b1
  a1 <- debruijn b2
  return $ AP a a1

debruijn (Abs x f) = do
  a <- local (((x,0):) . plus1) $ debruijn f 
  return $ LAM a

plus1 = map $ \(x, y) -> (x, y + 1)

-- alphaEq of two type
alphaEq :: Exp -> Exp -> Bool
alphaEq t1 t2 =
    let t1' = foldl' (\t x -> Forall x t) t1 (free t1)
        t2' = foldl' (\t x -> Forall x t) t2 (free t1) in
    runReader (debruijn t1') [] == runReader (debruijn t2') []



type GVar a = State Int a

type Subst = [(Name, Exp)]
-- kind level sub
applyK :: [(Name, Kind)] -> Kind -> Kind
applyK s Star = Star
applyK s Formula = Formula
applyK s (KVar x) = case lookup x s of
                       Just t -> t
                       Nothing -> (KVar x)
applyK s (KArrow k1 k2) = KArrow (applyK s k1) (applyK s k2)
-- both type level and evidence level substitution
applyE :: Subst -> Exp -> Exp
applyE [] e = e
applyE ((n,t):xs) e = applyE xs $ runSubst t (Var n) e

runSubst :: Exp -> Exp -> Exp -> Exp
runSubst t x t1 = fst $ runState (subst t x t1) 0
  
subst :: Exp -> Exp -> Exp -> GVar Exp
subst s (Var x) (Const y) = return $ Const y

subst s (Var x) (Var y) =
  if x == y then return s else return $ Var y
                               
subst s (Var x) (Imply f1 f2) = do
  c1 <- subst s (Var x) f1
  c2 <- subst s (Var x) f2
  return $ Imply c1 c2

subst s (Var x) (App f1 f2) = do
  c1 <- subst s (Var x) f1
  c2 <- subst s (Var x) f2
  return $ App c1 c2

subst s (Var x) (TApp f1 f2) = do
  c1 <- subst s (Var x) f1
  c2 <- subst s (Var x) f2
  return $ TApp c1 c2

subst s (Var x) (PApp f1 f2) = do
  c1 <- subst s (Var x) f1
  c2 <- subst s (Var x) f2
  return $ PApp c1 c2

subst s (Var x) (Forall a f) =
  if x == a || not (x `elem` free f) then return $ Forall a f
  else if not (a `elem` free s)
       then do
         c <- subst s (Var x) f
         return $ Forall a c
       else do
         n <- get
         modify (+1)
         c1 <- subst (Var (a++ show n)) (Var a) f
         subst s (Var x) (Forall (a ++ show n) c1)

subst s (Var x) (Abs a f) =
  if x == a || not (x `elem` free f) then return $ Abs a f
  else if not (a `elem` free s)
       then do
         c <- subst s (Var x) f
         return $ Abs a c
       else do
         n <- get
         modify (+1)
         c1 <- subst (Var (a++ show n)) (Var a) f
         subst s (Var x) (Abs (a ++ show n) c1)

subst s (Var x) (Lambda a Nothing f) =
  if x == a || not (x `elem` free f) then return $ Lambda a Nothing f
  else if not (a `elem` free s)
       then do
         c <- subst s (Var x) f
         return $ Lambda a Nothing c
       else do
         n <- get
         modify (+1)
         c1 <- subst (Var (a++ show n)) (Var a) f
         subst s (Var x) (Lambda (a ++ show n) Nothing c1)         


subst p (Var x) (Lambda y (Just t) p1) =
  if x == y || not (x `elem` free p1)
    then do
    t1 <- subst p (Var x) t
    return $ Lambda y (Just t1) p1
    else if not (y `elem` free p)
         then do
           t1 <- subst p (Var x) t
           c <- subst p (Var x) p1
           return $ Lambda y (Just t1) c
         else do
           n <- get
           modify (+1)
           c1 <- subst (Var (y++ show n)) (Var y) p1
           subst p (Var x) (Lambda (y++ show n) (Just t) c1)
           
-- normalize type expresion
normalize :: Exp -> Exp
-- normalize r | trace ("normalize " ++ show r) False = undefined
normalize (Var a) = Var a
-- normalize Star = Star
normalize (Const a) = Const a
normalize (Abs x t) = Abs x (normalize t)
normalize (PApp (Abs x t') t) = runSubst t (Var x) t'
normalize (PApp (Var x) t) = PApp (Var x) (normalize t)
normalize (PApp (Const x) t) = PApp (Const x) (normalize t)
normalize (PApp t' t) = case (PApp (normalize t') (normalize t)) of
                              a@(PApp (Abs x t') t) -> normalize a
                              b -> b
normalize (Imply t t') = Imply (normalize t) (normalize t')
normalize (Forall x t) = Forall x (normalize t)

  
