{-# LANGUAGE  ScopedTypeVariables, PatternGuards, StandaloneDeriving, DeriveDataTypeable #-}
module Main where
import Cegt.Parser
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
import Data.Tree
import qualified Control.Exception as E
import Control.Monad.State.Strict
import System.Environment
import System.Exit
import System.IO(withFile,hGetContents,IOMode(..),hClose,openFile)
import System.Console.Haskeline


main :: IO ()
main = evalStateT (runInputT defaultSettings loop) emptyEnv
  where
    loop :: InputT (StateT Env IO) ()
    loop = do
      minput <- getInputLine "cegt> "
      case minput of
        Nothing -> return ()
        Just ":q" -> return ()
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
                --                 outputStrLn (show $ )
                                 loop
                _ -> do outputStrLn $ "not enough argument for :loop "
                        loop
                        
                   | Just rest <- stripPrefix ":l " input ->
              do let filename:[] = words rest
                 lift (loadFile filename)
                 loop
                   | otherwise -> do outputStrLn $ "Unrecognize input : " ++ input
                                     loop


loadFile :: FilePath -> (StateT Env IO) ()
loadFile filename = do cnts <- lift (readFile filename)
                       case parseModule filename cnts of
                         Left e ->  lift (print (disp e $$ text ("fail to load file "++filename)))
                         Right a -> do modify (\ s -> extendMod a s)
                                       lift $ print (text ("loaded: "++filename))
                                       lift $ print (disp a)

                           where extendMod [] s = s
                                 extendMod ((n, e):xs) s = extendMod xs (extendAxiom n e s)
  

