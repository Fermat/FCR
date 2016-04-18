{-# LANGUAGE  ScopedTypeVariables, PatternGuards #-}
module Main where
-- 
import Cegt.Parser
import Cegt.Monad
import Cegt.Syntax
import Cegt.PrettyPrinting

import Control.Monad.Except hiding (join)
import Text.PrettyPrint
import Text.Parsec(ParseError)
import System.Console.CmdArgs
import Data.Typeable
import Data.List
import qualified Control.Exception as E
import Control.Monad.State
import System.Environment
import System.Exit
import System.IO(withFile,hGetContents,IOMode(..),hClose,openFile)
import Data.Map
import System.Console.Haskeline


main :: IO ()
main = runInputT defaultSettings loop'
  where
    loop' = undefined
    loop :: InputT (StateT Env IO) ()
    loop = do
      minput <- getInputLine "cegt> "
      case minput of
        Nothing -> return ()
        Just ":q" -> return ()
        Just input | Just rest <- stripPrefix ":e " input -> 
            do outputStrLn $ "the term was: " ++ rest
               loop

                   | Just filename <- stripPrefix ":l " input ->
              do mod <- lift $ loadFile filename
                 outputStrLn $ "loaded " ++ filename
                 loop
                   | otherwise -> do outputStrLn $ "Unrecognize input : " ++ input
                                     loop

-- loadFile :: FilePath -> IO Module
loadFile filename = flip E.catches handlers $
           do cnts <- readFile filename
              case parseModule filename cnts of
                   Left e -> E.throw e
                   Right a -> do putStrLn $ "Parsing success! \n"
                                 print $ disp a
                                 return a
                where handlers = [E.Handler parseHandler] 
                      parseHandler (e :: ParseError)= print (disp e) >> exitFailure      

{-
main = flip catches handlers $ do
  args <- getArgs
  case args of
    [filename] -> do
      cnts <- readFile filename
      case parseModule filename cnts of
             Left e -> throw e
             Right a -> do putStrLn $ "Parsing success! \n"
                           print $ disp a
    _ -> putStrLn "usage: cegt <filename>"
  where handlers = [Handler parseHandler] -- , Handler typeHandler
--        typeHandler e@(ErrMsg _) = print (disp e) >> exitFailure
        parseHandler (e :: ParseError)= print (disp e) >> exitFailure

liftEither (Left err) = throw err
liftEither (Right val) = return val
-}
