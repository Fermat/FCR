module IProver where

import Cegt.Syntax
import Cegt.PrettyPrinting
import Control.Monad.State.Strict
import Cegt.Monad
import Cegt.Syntax
import Data.List
import Cegt.Parser
import Cegt.Rewrite
import Cegt.Interaction

import Text.PrettyPrint
import System.Console.Haskeline


prover :: InputT (StateT (ProofState) IO) ()
prover  = do
          minput <- getInputLine "> "
          case minput of
            Nothing -> return ()
            Just input | Just rest <- stripPrefix "goal " input ->
              case parseExp rest of
                    Left err -> do
                      outputStrLn (show (disp err $$ text ("fail to parse expression "++ input)))
                      prover
                    Right e -> do
                      (gamma, _, _) <- (lift get)
                      let
                        -- gamma = (toFormula $ axioms env) ++ lemmas env
                        init = (gamma, e, [([], e)])
                      lift $ put init
                      outputStrLn $ "set to prove goal: " ++ (show $ disp e)
                      outputStrLn $ "in the environment:\n" ++ (show $ gamma)
                      prover
            Just input | Just rest <- stripPrefix "intros " input ->
              do let a = words rest
                 lift (modify (\ y -> intros y a))
                 (new, pf, (_,newGoal):_) <- lift get
                 outputStrLn $ "current goal: " ++ (show $ disp newGoal)
                 outputStrLn $ "in the environment:\n" ++ (show $ disp new)
                 outputStrLn $ "current mix proof term: " ++ (show $ disp pf)
                 prover
            Just input | Just rest <- stripPrefix "coind " input ->
              do s <- lift get
                 case coind rest s of
                   Nothing -> outputStrLn $ "coind tactic can only be used at the very beginning of the proof"
                   Just s'@(ns, _, (_,g):_) ->
                     do lift $ put s'
                        outputStrLn $ "current goal: " ++ (show $ disp g)
                        outputStrLn $ "in the environment:\n " ++ (show $ disp ns)
                        prover

            Just input | Just rest <- stripPrefix "apply " input ->
              case parseExp rest of
                Left err -> do
                      outputStrLn (show (disp err))
                      prover
                Right big -> do
                  case flatten big of
                    ((Const n):ins) -> do 
                      s <- lift get
                      case apply s n ins of
                        Nothing -> do outputStrLn $ "fail to apply rule: " ++ (show n)
                                      prover
                        Just s'@(gamma,pf,[]) ->
                          do outputStrLn $ "QED with the proof:\n " ++ (show $ disp pf)
                             outputStrLn $ "in the environment:\n " ++ (show $ disp gamma)
                             prover
                        Just s'@(gamma,pf,(_,g):_ ) ->
                          do lift $ put s'
                             outputStrLn $ "current goal: " ++ (show $ disp g)
                             outputStrLn $ "in the environment: " ++ (show $ disp gamma)
                             outputStrLn $ "current mix proof term: " ++ (show $ disp pf)
                             prover
                    ((Var n):ins) -> do 
                      s <- lift get
                      -- outputStrLn $ (show ((Var n):ins))
                      -- outputStrLn $ show s
                      case apply s n ins of
                        Nothing -> do outputStrLn $ "fail to apply rule: " ++ (show n)
                                      prover
                        Just s'@(gamma,pf,[]) ->
                          do outputStrLn $ "QED with the proof:\n " ++ (show $ disp pf)
                             outputStrLn $ "in the environment:\n " ++ (show $ disp gamma)
                             prover
                        Just s'@(gamma,pf,(_,g):_ ) ->
                          do lift $ put s'
                             outputStrLn $ "current goal: " ++ (show $ disp g)
                             outputStrLn $ "in the environment: " ++ (show $ disp gamma)
                             outputStrLn $ "current mix proof term: " ++ (show $ disp pf)
--                             outputStrLn $ show s'
                             prover         
                    a -> do  outputStrLn $ "wrong input: " ++ (show a)
                             prover
            Just input | Just rest <- stripPrefix "end" input -> return ()
                             
            Just input -> do
              outputStrLn $ "unrecognized input "++ (show input)
              prover
