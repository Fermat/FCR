{-# LANGUAGE  ScopedTypeVariables, PatternGuards, StandaloneDeriving, DeriveDataTypeable #-}
module Main where
import Cegt.Parser
import Cegt.Interaction
import Cegt.Loop
import Cegt.Rewrite
import Cegt.Monad
import Cegt.Syntax
import Cegt.PrettyPrinting

import Control.Monad.Except hiding (join)
import Text.PrettyPrint
import Text.Parsec(ParseError)
import System.Console.CmdArgs
import Data.Typeable
import Data.List
import Data.Tree hiding (flatten)
import qualified Control.Exception as E
import Control.Monad.State.Strict
import System.Environment
import System.Exit
import System.IO(withFile,hGetContents,IOMode(..),hClose,openFile)
import System.Console.Haskeline


main :: IO ()
main = evalStateT (evalStateT (runInputT defaultSettings loop) emptyEnv) ([], Var "dummy", [])
  where
    loop :: InputT (StateT Env (StateT ([(Name, Exp)], Exp, [(Pos, Exp)]) IO)) ()
    loop = do
      minput <- getInputLine "cegt> "
      case minput of
        Nothing -> return ()
        Just ":q" -> return ()
        Just ":iprover" -> prover >> loop
        Just input | Just rest <- stripPrefix ":outer " input ->
            do let l = words rest
               case l of
                n:xs -> 
                  case parseExp (unwords xs) of
                    Left err -> do
                      outputStrLn (show (disp err $$ text ("fail to parse expression "++ (unwords xs))))
                      loop
                    Right e -> 
                          do state <- lift get
                             let num = read n :: Int
                                 res = getTrace (axioms state) e num
                             outputStrLn $ "the execution trace is:\n " ++ (show $ disp res)
                             loop
                _ -> do outputStrLn $ "not enough argument for :outer "
                        loop
        Just input | Just rest <- stripPrefix ":inner " input ->
            do let l = words rest
               case l of
                n:xs -> 
                  case parseExp (unwords xs) of
                    Left err -> do
                      outputStrLn (show (disp err $$ text ("fail to parse expression "++ (unwords xs))))
                      loop
                    Right e -> 
                          do state <- lift get
                             let num = read n :: Int
                                 res = getTrace' (axioms state) e num
                             outputStrLn $ "the execution trace is:\n " ++ (show $ disp res)
                             loop
                _ -> do outputStrLn $ "not enough argument for :inner "
                        loop
        Just input | Just rest <- stripPrefix ":full " input ->
            do let l = words rest
               case l of
                n:xs -> 
                  case parseExp (unwords xs) of
                    Left err -> do
                      outputStrLn (show (disp err $$ text ("fail to parse expression "++ (unwords xs))))
                      loop
                    Right e -> 
                          do state <- lift get
                             let num = read n :: Int
                                 redTree = reduce (axioms state) ([], "_", e) num
                                 pTree = dispTree redTree
                             outputStrLn $ "the execution tree is:\n " ++ (drawTree pTree)
                             loop
                _ -> do outputStrLn $ "not enough argument for :inner "
                        loop
        Just input | Just rest <- stripPrefix ":partial " input ->
            do let l = words rest
               case l of
                n:xs -> 
                  case parseExp (unwords xs) of
                    Left err -> do
                      outputStrLn (show (disp err $$ text ("fail to parse expression "++ (unwords xs))))
                      loop
                    Right e -> 
                          do state <- lift get
                             let num = read n :: Int
                                 res = getTrace' (axioms state) e num
                                 pf = partial res
                             outputStrLn $ "the execution trace is:\n " ++ (show $ disp res)
                             outputStrLn $ "the partial proof is:\n " ++ (show $ disp pf)
                             loop
                _ -> do outputStrLn $ "not enough argument for :partial "
                        loop
        Just input | Just rest <- stripPrefix ":loop " input ->
            do let l = words rest
               case l of
                n:xs -> 
                  case parseExp (unwords xs) of
                    Left err -> do
                      outputStrLn (show (disp err $$ text ("fail to parse expression "++ (unwords xs))))
                      loop
                    Right e -> 
                          do state <- lift get
                             let num = read n :: Int
                                 res = getTrace' (axioms state) e num
                                 pf = constrLoop res
                             outputStrLn $ "the execution trace is:\n " ++ (show $ disp res)
                             case pf of
                               [] -> do outputStrLn $ "fail to construct proof.\n "
                                        loop
                               (n1,e1):(n2,e2):[] -> do
                                 outputStrLn $ "the proof is:\n " ++ (show $ text n1 <+> text "=" <+>disp e1 $$ (text n2 <+> text "=" <+>disp e2))
                                 loop
                _ -> do outputStrLn $ "not enough argument for :loop "
                        loop
                   | Just rest <- stripPrefix ":l " input ->
              do let filename:[] = words rest
                 lift (loadFile filename)
                 loop
                   | otherwise -> do outputStrLn $ "Unrecognize input : " ++ input
                                     loop


prover :: InputT (StateT Env (StateT ([(Name, Exp)], Exp, [(Pos, Exp)]) IO)) ()
prover = do
          minput <- getInputLine "> "
          case minput of
            Nothing -> return ()
            Just input | Just rest <- stripPrefix "goal " input ->
              case parseExp rest of
                    Left err -> do
                      outputStrLn (show (disp err $$ text ("fail to parse expression "++ input)))
                      prover
                    Right e -> do
                      state <- (lift get)
                      let
                        gamma = (toFormula $ axioms state) ++ lemmas state
                        init = (gamma, e, [([], e)])
                      lift (lift $ put init)
                      outputStrLn $ "set to prove goal: " ++ (show $ disp e)
                      outputStrLn $ "in the environment:\n" ++ (show $ disp gamma)
                      prover
            Just input | Just rest <- stripPrefix "intros " input ->
              do let a = words rest
                 lift $ lift (modify (\ y -> intros y a))
                 (new, pf, (_,newGoal):_) <- lift (lift get)
                 outputStrLn $ "current goal: " ++ (show $ disp newGoal)
                 outputStrLn $ "in the environment:\n" ++ (show $ disp new)
                 prover
            Just input | Just rest <- stripPrefix "coind " input ->
              do s <- lift (lift get)
                 case coind rest s of
                   Nothing -> outputStrLn $ "coind tactic can only be used at the very beginning of the proof"
                   Just s'@(ns, _, (_,g):_) ->
                     do lift (lift (put s'))
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
                      s <- lift (lift get)
                      case apply s n ins of
                        Nothing -> do outputStrLn $ "fail to apply rule: " ++ (show n)
                                      prover
                        Just s'@(gamma,pf,[]) ->
                          do outputStrLn $ "QED with the proof:\n " ++ (show $ disp pf)
                             outputStrLn $ "in the environment:\n " ++ (show $ disp gamma)
                             prover
                        Just s'@(gamma,pf,(_,g):_ ) ->
                          do lift (lift (put s'))
                             outputStrLn $ "current goal: " ++ (show $ disp g)
                             outputStrLn $ "in the environment: " ++ (show $ disp gamma)
                             prover
                    ((Var n):ins) -> do 
                      s <- lift (lift get)
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
                          do lift (lift (put s'))
                             outputStrLn $ "current goal: " ++ (show $ disp g)
                             outputStrLn $ "in the environment: " ++ (show $ disp gamma)
                             prover         
                    a -> do  outputStrLn $ "wrong input: " ++ (show a)
                             prover
            Just input | Just rest <- stripPrefix "end" input -> return ()
                             
            Just input -> do
              outputStrLn $ "unrecognized input "++ (show input)
              prover

loadFile :: FilePath -> (StateT Env (StateT ([(Name, Exp)], Exp, [(Pos, Exp)]) IO)) ()
loadFile filename = do cnts <- lift (lift (readFile filename))
                       case parseModule filename cnts of
                         Left e ->  lift $ lift (print (disp e $$ text ("fail to load file "++filename)))
                         Right a -> do modify (\ s -> extendMod a s)
                                       lift $ lift $ print (text ("loaded: "++filename))
                                       lift $ lift $ print (disp a)

                           where extendMod [] s = s
                                 extendMod ((n, e):xs) s = extendMod xs (extendAxiom n e s)
  

