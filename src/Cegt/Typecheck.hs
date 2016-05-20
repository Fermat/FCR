module Cegt.Typecheck where

import Cegt.Syntax
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
runKinding t g = runReaderT (evalStateT (evalStateT (inferKind t) 0) []) g

ground :: Kind -> Kind
ground (KVar x) = Star
ground (KArrow k1 k2) = KArrow (ground k1) (ground k2)
ground Star = Star
ground Formula = Formula

inferKind :: Exp -> KCMonad Kind
inferKind (Const x) = do
  genv <- ask
  case lookup x genv of
    Just k -> return k
    Nothing -> lift $ lift $ lift $ Left $ text "Kinding error: " <+> text "undefine type constructor:" <+> disp x
  
inferKind (Var x) = do
  env <- lift get
  case lookup x env of
    Nothing -> do
      ki <- makeName "k"
      let kind = KVar ki
      lift $ modify (\ e -> (x, kind): e)
      return kind
    Just k -> return k  
  
inferKind (App f1 f2) = do
  k1 <- inferKind f1
  k2 <- inferKind f2
  unificationK k2 Star
  k <- makeName "k"
  unificationK k1 $ KArrow Star (KVar k) 
  return (KVar k) 

inferKind (Lambda x t) = do
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

applyK :: [(Name, Kind)] -> Kind -> Kind
applyK _ Star = Star
applyK _ Formula = Formula
applyK subs (KVar x) =
  case lookup x subs of
    Just x1 -> x1
    Nothing -> KVar x

applyK subs (KArrow Star f2) =
  let a2 = applyK subs f2 in
  KArrow Star a2
