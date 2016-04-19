{-# LANGUAGE  ScopedTypeVariables, PatternGuards, StandaloneDeriving, DeriveDataTypeable #-}
module Main where
import Cegt.Parser
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
import qualified Control.Exception as E
import Control.Monad.State.Strict
import System.Environment
import System.Exit
import System.IO(withFile,hGetContents,IOMode(..),hClose,openFile)
-- import Data.Map
import System.Console.Haskeline



-- main :: IO ()
-- main = runInputT defaultSettings loop
--    where 
--        loop :: InputT IO ()
--        loop = do
--            minput <- getInputLine "% "
--            case minput of
--                Nothing -> return ()
--                Just "quit" -> return ()
--                Just input -> do outputStrLn $ "Input was: " ++ input
-- loop

-- instance MonadException (StateT Int IO)

main :: IO ()
main = evalStateT (runInputT defaultSettings loop) emptyEnv
  where
    loop :: InputT (StateT Env IO) ()
    loop = do
      minput <- getInputLine "cegt> "
      case minput of
        Nothing -> return ()
        Just ":q" -> return ()
        Just input | Just rest <- stripPrefix ":e " input ->
            do let l = words rest
               case l of
                x:n:[] -> 
                  case parseExp x of
                    Left err -> do outputStrLn (show (disp err $$ text ("fail to parse expression "++x)))
                                   loop
                    Right e -> 
                          do state <- lift get
                             let num = read n :: Int
                                 res = steps (axioms state) e num
                             outputStrLn $ "the result of evaluation is: " ++ (show $ disp res)
                             loop
                _ -> do outputStrLn $ "unknown argument for :e " ++ (unwords l)
                        loop
                   | Just filename <- stripPrefix ":l " input ->
              do lift (loadFile filename)
                 loop
                   | otherwise -> do outputStrLn $ "Unrecognize input : " ++ input
                                     loop


-- instance Exception Doc
-- deriving instance Typeable Doc

loadFile :: FilePath -> (StateT Env IO) ()
loadFile filename = do cnts <- lift (readFile filename)
                       case parseModule filename cnts of
                         Left e ->  lift (print (disp e $$ text ("fail to load file "++filename)))
                         Right a -> do modify (\ s -> extendMod a s)
                                       lift $ print (text ("loaded: "++filename))
                                       lift $ print (disp a)

                           where extendMod [] s = s
                                 extendMod ((n, e):xs) s = extendMod xs (extendAxiom n e s)
  


  -- $ flip E.catches handlers $
  --          do cnts <- readFile filename
  --             case parseModule filename cnts of
  --                  Left e -> E.throw e
  --                  Right a -> do putStrLn $ "Parsing success! \n"
  --                                print $ disp a
  --                                return a
  --               where handlers = [E.Handler parseHandler] 
  --                     parseHandler (e :: ParseError)= print (disp e) >> exitFailure      

