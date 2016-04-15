{-# LANGUAGE  ScopedTypeVariables #-}
module Main where
import Cegt.Parser
import Cegt.Syntax
import Cegt.PrettyPrinting

import Control.Monad.Except hiding (join)
import Text.PrettyPrint
import Text.Parsec(ParseError)
import System.Console.CmdArgs
import Data.Typeable
import Control.Exception
import Control.Monad.State
import System.Environment
import System.Exit
import System.IO(withFile,hGetContents,IOMode(..),hClose,openFile)
import Data.Map
import System.Console.Haskeline


main :: IO ()
main = runInputT defaultSettings loop
  where 
    loop :: InputT IO ()
    loop = do
      minput <- getInputLine "cegt> "
      case minput of
        Nothing -> return ()
        Just "quit" -> return ()
        Just input -> do -- outputStrLn $ "Input was: " ++ input
                         
                         loop

handle a = if a == (":l "++res) then 
             
           



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
