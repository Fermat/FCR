{-# LANGUAGE NamedFieldPuns, DeriveDataTypeable, ParallelListComp, GeneralizedNewtypeDeriving, FlexibleInstances, FlexibleContexts  #-}
module Cegt.Monad where
import Cegt.Syntax
import Cegt.PrettyPrinting

import Text.PrettyPrint
import Data.Typeable
import Control.Monad.State
import Control.Monad.Except
import Control.Exception
import qualified Data.Map as M
-- import Control.Applicative hiding (empty)
import Control.Monad.Reader
import Text.Parsec.Pos
import Data.List

data Env = Env{axioms :: [(Name, Exp)],
               lemmas :: [(Name, (Exp, Exp))], -- (name, (proof, formula))
               rules :: [(Name, Exp)],
               tacs :: [((Name, Exp), [Tactic])],
               kinds ::[(Name, Kind)],
               pfdecls ::[(Name, Exp, Exp)] -- (name, formula, proof)
              }
         deriving Show

constKinds :: [(Name, Exp)] -> [(Name, Kind)]
constKinds rules =
  let res = concat $ map (\ (_, t) -> helper t) rules
  in nub $ res
  where  helper (Arrow t1 t2) = getKinds t1 ++ getKinds t2
         helper (a@(Forall x t)) = helper $ viewFBody a
         helper (Imply t1 t2) = helper t1 ++ helper t2
         helper a = getKinds a
         
getKinds :: Exp -> [(Name, Kind)]
getKinds t = case flatten t of
                (Const x):xs -> let arity = length xs
                                    k = aToKind arity in
                                (x, k):(concat $ map getKinds xs)
                (Var x):xs -> concat $ map getKinds xs
                _ -> error "impossible happens in getKinds function"
                                    

aToKind :: Int -> Kind
aToKind n | n == 0 = Star
           | n > 0 = KArrow Star (aToKind (n-1))
                     
instance Disp Env where
  disp (Env as lms rs ts ks pfs) =
    text "rewrite rules" $$ (vcat  (map (\ (n, exp) -> disp n <+> text ":" <+> disp exp) rs)) $$
    text "kinds" $$ (vcat  (map (\ (n, exp) -> disp n <+> text ":" <+> disp exp) ks)) $$
    text "axioms" $$ (vcat  (map (\ (n, exp) -> disp n <+> text ":" <+> disp exp) as)) $$ 
    text "proof declarations" $$ (sep (map (\ (n, exp, pf) -> (disp n <+> text ":" <+> disp exp <+> text "=") $$ disp pf) pfs)) $$
    text "lemmas" $$ (vcat (map (\ (n, (pf, exp)) -> (disp n <+> text ":" <+> disp exp <+> text "=") $$ disp pf) lms)) 
                         -- $$ text "textual lemma" $$
                         -- (vcat (map
                         --        (\ ((n, exp),pfs) ->
                         --          (disp n <+> text ":" <+> disp exp) $$ (vcat (map disp pfs)))
                         --        ts))
                      

emptyEnv :: Env
emptyEnv = Env {axioms = [], lemmas = [], rules = [], tacs = [], kinds = [], pfdecls = []}
                  
extendAxiom :: Name -> Exp -> Env -> Env
extendAxiom v ts e@(Env {axioms}) = e{axioms =  (v , ts) : axioms}

extendLemma :: Name -> Exp -> Exp -> Env -> Env
extendLemma v pf t e@(Env {lemmas}) = e{lemmas = (v, (pf, t)):lemmas}

extendRule :: Name -> Exp -> Env -> Env
extendRule v ts e@(Env {rules}) = e{rules =  (v , ts) : rules}

extendTac :: Name -> Exp -> [Tactic] -> Env -> Env
extendTac v es ts e@(Env {tacs}) = e{tacs =  ((v, es), ts) : tacs}

addKinds :: [(Name, Kind)] -> Env -> Env
addKinds ks e@(Env {kinds}) = e{kinds = ks}

addDecls :: [(Name, Exp, Exp)] -> Env -> Env
addDecls ks e@(Env {pfdecls}) = e{pfdecls = ks}
