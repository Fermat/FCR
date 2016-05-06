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

type History = [ProofState]

prover :: InputT (StateT (Exp, History, ProofState) IO) (Maybe (Name, Exp, Exp))
prover  = do
          minput <- getInputLine "> "
          case minput of
            Nothing -> return Nothing
            Just input | Just rest <- stripPrefix "goal " input ->
              case parseExp rest of
                    Left err -> do
                      outputStrLn (show (disp err $$ text ("fail to parse expression "++ rest)))
                      prover
                    Right e -> do
                      case flatten e of
                        (Var g):exp:[] -> 
                          do (_, [], (_, _, (_,_,gamma):_)) <- lift get
                             let init = (g, exp, [([], exp, gamma)])
                             lift $ put (exp, [], init)
                             outputStrLn $ "set to prove goal " ++ g ++ " : \n" ++ (show $ disp exp)
                             outputStrLn $ "in the environment:\n" ++ (show $ gamma)
                             prover
                        _ -> do outputStrLn $ "wrong format for the tactic goal \n"
                                prover
            Just input | Just rest <- stripPrefix "intros " input ->
              do let a = words rest
                 (gf, hist, st1) <- lift get
                 let st2@(_, pf, (_,newGoal, new):_) = intros st1 a
                 lift (put (gf, st1:hist, st2))
                 outputStrLn $ "current goal: " ++ (show $ disp newGoal)
                 outputStrLn $ "in the environment:\n" ++ (show $ disp new)
                 outputStrLn $ "current mix proof term: " ++ (show $ disp pf)
                 prover
            Just "undo" ->
              do (gf, hist, s) <- lift get
                 case hist of
                   [] -> do outputStrLn $ "cannot further undo"
                            prover
                   (h@(_,pf,(_,g,ns):_)):xs ->
                     do lift (put (gf, xs, h))
                        outputStrLn $ "current goal: " ++ (show $ disp g)
                        outputStrLn $ "in the environment: " ++ (show $ disp ns)
                        outputStrLn $ "current mix proof term: " ++ (show $ disp pf)
                        prover
            Just "coind" ->
              do (gf, hist, s) <- lift get
                 case coind s of
                   Nothing -> 
                     do outputStrLn $ "coind tactic can only be used at the very beginning of the proof"
                        prover
                   Just s'@(_, _, (_,g,ns):_) ->
                     do lift $ put (gf, s:hist, s')
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
                      (gf, hist, s@(_,_,(_,_,gamma):_)) <- lift get
                      case apply s n ins of
                        Nothing -> do outputStrLn $ "fail to apply rule: " ++ (show n)
                                      prover
                        Just s'@(gn,pf,[]) ->
                          do
                             lift $ put (gf, s:hist, s')
                             outputStrLn $ "QED with the proof:\n " ++ (show $ disp pf)
                             outputStrLn $ "in the environment:\n " ++ (show $ disp gamma)
                             return $ Just (gn,pf,gf)
                        Just s'@(_,pf,(_,g,gamma):_ ) ->
                          do lift $ put (gf, s:hist, s')
                             outputStrLn $ "current goal: " ++ (show $ disp g)
                             outputStrLn $ "in the environment: " ++ (show $ disp gamma)
                             outputStrLn $ "current mix proof term: " ++ (show $ disp pf)
                             prover
                    ((Var n):ins) -> do
                      (gf, hist, s@(_,_,(_,_,gamma):_)) <- lift get
                      case apply s n ins of
                        Nothing -> do outputStrLn $ "fail to apply rule: " ++ (show n)
                                      prover
                        Just s'@(gn,pf,[]) ->
                          do
                             lift $ put (gf, s:hist, s')
                             outputStrLn $ "QED with the proof:\n " ++ (show $ disp pf)
                             outputStrLn $ "in the environment:\n " ++ (show $ disp gamma)
                             return $ Just (gn,pf,gf)
                        Just s'@(_,pf,(_,g,gamma):_ ) ->
                          do lift $ put (gf, s:hist, s')
                             outputStrLn $ "current goal: " ++ (show $ disp g)
                             outputStrLn $ "in the environment: " ++ (show $ disp gamma)
                             outputStrLn $ "current mix proof term: " ++ (show $ disp pf)
                             prover
                    a -> do  outputStrLn $ "wrong input: " ++ (show a)
                             prover
            Just input | Just rest <- stripPrefix "end" input -> return Nothing

                             
            Just input -> do
              outputStrLn $ "unrecognized input "++ (show input)
              prover
