module Main where
import Fcr.Parser
import Fcr.Typecheck
-- import Fcr.Reduction
import Fcr.Typeinfer
import Fcr.Eval
import Fcr.Rewrite hiding (steps)
import Fcr.Monad
import Fcr.Syntax
import Fcr.PrettyPrinting

import Control.Monad.Except hiding (join)
import Text.PrettyPrint hiding (semi)
import Text.Parsec(ParseError)
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
main = evalStateT (runInputT defaultSettings loop) emptyEnv
  where
    loop :: InputT (StateT Env IO) ()
    loop = do
      input <- getInputLine "fcr> "
      case input of
        Nothing -> return ()
        Just ":q" -> return ()
        Just others -> do
          let ws = words others
          dispatch ws
          loop

dispatch :: [String] -> InputT (StateT Env IO) ()
dispatch [":env"] = do env <- lift get
                       outputStrLn $ show (text "the current environment" $$ disp env)

dispatch (":outer":n:exp) =
  let num = read n :: Int in
    case parseExp (unwords exp) of
      Left err -> outputStrLn (show (disp err $$ text ("fail to parse expression "++ unwords exp)))
      Right e -> do env <- lift get
                    let res = getTrace (rules env) e num
                    outputStrLn $ "the execution trace is:\n " ++ show (disp res)

dispatch (":inner":n:exp) =
  let num = read n :: Int in
    case parseExp (unwords exp) of
      Left err -> outputStrLn (show (disp err $$ text ("fail to parse expression "++ unwords exp)))
      Right e -> do env <- lift get
                    let res = getTrace' (rules env) e num
                    outputStrLn $ "the execution trace is:\n " ++ show (disp res)

dispatch (":full":n:exp) =
  let num = read n :: Int in
    case parseExp (unwords exp) of
      Left err -> outputStrLn (show (disp err $$ text ("fail to parse expression "++ unwords exp)))
      Right e -> do env <- lift get
                    let redTree = reduce (rules env) ([], "_", e) num
                        pTree = dispTree redTree
                    outputStrLn $ "the execution tree is:\n " ++ drawTree pTree

dispatch [":l", filename] = lift (put emptyEnv) >> lift (loadFile filename)
               
dispatch xs = outputStrLn $ "Unrecognize input : " ++ unwords xs                  


loadFile :: FilePath -> StateT Env IO ()
loadFile filename =
  do cnts <- lift (readFile filename)
     case parseModule filename cnts of
       Left e -> lift $ print (disp e $$ text ("fail to load file "++filename))
       Right a ->
         do let bindings = decls a
                rs = getRules bindings
                ax = getAxioms bindings  
                ks = constKinds bindings
                pdl = pfDecl a
                sts = modsteps a
                env = Env{axioms = toFormula rs ++ ax, lemmas = [], rules = rs, tacs = [],
                          kinds = ks, pfdecls = pdl, steps = sts} 
            let res = foldM semi env pdl
            case res of
              Left err -> lift $ print (disp err)
              Right env' -> do put env'
                               lift $ print (disp env')
                               lift $ print (text "automated proof reconstruction success!")
                               evaluation
            

                              
evaluation :: StateT Env IO ()
evaluation = do
  env <- get
  let ss = steps env
      res = mapM (\ (x, y) -> eval env y (Var x)) ss
  case res of
    Left err -> lift $ print err
    Right r ->  lift $ print (text "steps results" $$ vcat (map disp r))
      
semi :: Env -> (Name, Exp, Exp) -> Either Doc Env
semi env (n, f, pf) = 
    let ks = kinds env
        lms = map (\ (n,(_, e)) -> (n, e)) $ lemmas env
        as = axioms env
        pEnv = as ++ lms
        init = [(ks, n, f, [([], f, pf, (n, f):pEnv, [])], Nothing,0)] in
    do e <- ersm init -- constrProof init 
       let e' = rebind e
       runProofCheck n e' f env
       return $ extendLemma n e' f env

