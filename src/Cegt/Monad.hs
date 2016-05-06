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
import Control.Applicative hiding (empty)
import Control.Monad.Reader
import Text.Parsec.Pos


data Env = Env{axioms :: [(Name, Exp)],
               lemmas :: [(Name, (Exp, Exp))] -- (name, (proof, formula))
              }
         deriving Show

instance Disp Env where
  disp (Env as lms) = (vcat  (map (\ (n, exp) -> disp n <+> text ":" <+> disp exp) as)) $$
                      (vcat (map (\ (n, (pf, exp)) -> (disp n <+> text ":" <+> disp exp <+> text "=") $$ disp pf) lms))
  

emptyEnv :: Env
emptyEnv = Env {axioms = [], lemmas = []}
                  
extendAxiom :: Name -> Exp -> Env -> Env
extendAxiom v ts e@(Env {axioms}) = e{axioms =  (v , ts) : axioms}

extendLemma :: Name -> Exp -> Exp -> Env -> Env
extendLemma v pf t e@(Env {lemmas}) = e{lemmas = (v, (pf, t)):lemmas}
