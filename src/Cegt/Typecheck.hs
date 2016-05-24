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
runKinding t g = runReaderT (evalStateT (evalStateT (inferKind t) 0) []) g

runKinding' :: Exp -> KSubst -> Either Doc (Kind, KSubst)
runKinding' t g = runReaderT (runStateT (evalStateT (inferKind t) 0) []) g

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


type PCMonad a = (ReaderT [(Name, Exp)] (ReaderT KSubst (Either Doc))) a

-- use current axioms and lemmas to check more lemma 
runProofCheck :: Name -> Exp -> Exp -> Env -> Either Doc ()
runProofCheck n t f env = do
  let ev = (n, f) : (axioms env ++ (map (\ (x, (_, f)) -> (x, f)) $ lemmas env))
      ks = kinds env
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

proofCheck (Const x) = do env <- ask
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
                                 

proofCheck (Lambda x (Just t1) t) = do t <- local (\ y -> (x, t1) : y) (proofCheck t1)
                                       return $ Imply t1 t

proofCheck (Lambda x Nothing t) = do
  f <- proofCheck t
  e <- ask
  if isFree x e
    then lift $ lift $ Left $
         sep [text "proof checking error", text "generalized variable" <+> disp x, text "appears in the assumptions"]
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
                              (k1, _) <- lift $ lift $ runKinding' e2 ks
                              let k = ground k1
                              if isTerm k then
                                case f1 of
                                  Forall x a2 -> do
                                    (_, subs) <- lift $ lift $ runKinding' a2 ks
                                    case lookup x subs of
                                      Nothing -> lift $ lift $ Left $
                                                 sep [text "proof checking error",
                                                      text "vacuous abstraction on variable" <+> disp x,
                                                      text "in the type of" <+> disp e1,
                                                      text "its kind" <+> disp (Forall x a2)]
                                      Just k2 -> 
                                        if ground k2 == k
                                        then do let res = normalize $ runSubst e2 (Var x) a2
                                                kindable res ks   
                                                return res    
                                        else lift $ lift $ Left $
                                             sep [text "proof checking error:",
                                                  text "kind mismatch",
                                                  text "expected"<+> disp k,
                                                  text "actual kind" <+> disp (ground k2),
                                                  text "on the applicant of" <+> disp e1
                                                  ]

                                  b ->  lift $ lift $ Left $
                                        (text "proof checking error on"
                                         <+> disp e1) $$ (nest 2 $ text "unexpected type:" <+> disp b)
                                       
                                else lift $ lift $ Left $
                                     sep [text "proof checking error", text "ill-kinded expression:",
                                          disp e2]

isFree :: Name -> [(Name, Exp)] -> Bool
isFree x m = not (null (filter (\ y ->  x `elem` (free (snd y))) m))
                                       





