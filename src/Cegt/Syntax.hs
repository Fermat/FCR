module Cegt.Syntax where

import Control.Monad.State.Lazy
import Control.Monad.Reader

import Data.Char
import qualified Data.Set as S
import Data.List hiding (partition)


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

data Nameless = V Int
              | C Name
              | IMP Nameless Nameless
              | ALL Nameless
              | AP Nameless Nameless
              | LAM Nameless
             deriving (Show, Eq)
                   
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
freeVar (Lambda x f) = delete x (freeVar f)
freeVar (Imply b h) = freeVar b ++ freeVar h

flatten :: Exp -> [Exp]
flatten (App f1 f2) = flatten f1 ++ [f2]
flatten a = [a]


type BindCxt a = Reader [(Name, Int)] a

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

debruijn (App b1 b2) = do
  a <- debruijn b1
  a1 <- debruijn b2
  return $ AP a a1

debruijn (Lambda x f) = do
  a <- local (((x,0):) . plus1) $ debruijn f 
  return $ LAM a

plus1 = map $ \(x, y) -> (x, y + 1)


alphaEq :: Exp -> Exp -> Bool
alphaEq t1 t2 =
    let t1' = foldl' (\t x -> Forall x t) t1 (free t1)
        t2' = foldl' (\t x -> Forall x t) t2 (free t1) in
    runReader (debruijn t1') [] == runReader (debruijn t2') []



type GVar a = State Int a

type Subst = [(Name, Exp)]

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

subst s (Var x) (Lambda a f) =
  if x == a || not (x `elem` free f) then return $ Lambda a f
  else if not (a `elem` free s)
       then do
         c <- subst s (Var x) f
         return $ Lambda a c
       else do
         n <- get
         modify (+1)
         c1 <- subst (Var (a++ show n)) (Var a) f
         subst s (Var x) (Lambda (a ++ show n) c1)         

  
