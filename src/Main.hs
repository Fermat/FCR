{-# LANGUAGE ScopedTypeVariables #-}
module Main where
import Fcr.Parser
import Fcr.Typecheck
import Fcr.Typeinference
import Fcr.Interaction
import Fcr.Eval
import Fcr.Loop
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

dispatch [":outer",n,exp] =
  let num = read n :: Int in
    case parseExp exp of
      Left err -> outputStrLn (show (disp err $$ text ("fail to parse expression "++ exp)))
      Right e -> do env <- lift get
                    let res = getTrace (rules env) e num
                    outputStrLn $ "the execution trace is:\n " ++ (show $ disp res)

dispatch [":inner", n, exp] =
  let num = read n :: Int in
    case parseExp exp of
      Left err -> outputStrLn (show (disp err $$ text ("fail to parse expression "++ exp)))
      Right e -> do env <- lift get
                    let res = getTrace' (rules env) e num
                    outputStrLn $ "the execution trace is:\n " ++ (show $ disp res)

dispatch [":full", n, exp] =
  let num = read n :: Int in
    case parseExp exp of
      Left err -> outputStrLn (show (disp err $$ text ("fail to parse expression "++ exp)))
      Right e -> do env <- lift get
                    let redTree = reduce (rules env) ([], "_", e) num
                        pTree = dispTree redTree
                    outputStrLn $ "the execution tree is:\n " ++ (drawTree pTree)

dispatch [":l", filename] = lift (put emptyEnv) >> lift (loadFile filename)
               
dispatch xs = outputStrLn $ "Unrecognize input : " ++ unwords xs                  


loadFile :: FilePath -> StateT Env IO ()
loadFile filename = do cnts <- lift (readFile filename)
                       case parseModule filename cnts of
                         Left e ->
                           do lift $ print (disp e $$ text ("fail to load file "++filename))
                         Right a -> do let bindings = decls a
                                           rs = getRules bindings
                                           ax = getAxioms bindings  
                                           pfs = prfs a
                                           ks = constKinds bindings
                                           pdl = pfDecl a
                                           sts = modsteps a
                                       modify (\ s -> extendMod (toFormula rs ++ ax) s)
                                       modify (\ s -> extendR rs s)
                                       modify (\ s -> extendTacs pfs s)
                                       modify (\ s -> addKinds ks s)
                                       modify (\ s -> addDecls pdl s)
                                       modify (\ s -> addSteps sts s)
--                                       lift (print (show pfs))
                                       
                                       env <- get
                                       
                                       case interpret env pfs of
                                         Right res -> do
                                           let res' = mapM (\ (n, (p, exp)) -> runProofCheck n p exp env) res
                                           case res' of
                                             Left err -> lift $ print (disp err $$ text ("fail to load file "++filename))
                                             Right _ -> 
                                                 do modify (\ s -> extendLms res s)
                                                    lift $ print (text ("passed the interactive proof checker"))
                                                    env' <- get
                                                    semiauto
                                                    evaluation
                                                        

                                                    -- lift $ print (disp env')

                                                    
                                                    -- lift $ print (disp (lemmas env'))
                                         Left err ->
                                           lift $ print (text "error in the proof script:"
                                                         $$ disp err)
                                       
                           where extendMod [] s = s
                                 extendMod ((n, e):xs) s = extendMod xs (extendAxiom n e s)
                                 extendR [] s = s
                                 extendR ((n, e):xs) s = extendR xs (extendRule n e s)
                                 extendTacs [] s = s
                                 extendTacs (((n, e), ts):xs) s = extendTacs xs
                                                                  (extendTac n e ts s)
                                 extendLms [] s = s
                                 extendLms ((n, (p, e)):xs) s = extendLms xs
                                                                  (extendLemma n p e s)



evaluation :: StateT Env IO ()
evaluation = do
  env <- get
  let ss = steps env
      res = mapM (\ (x, y) -> eval env y (Var x)) ss
  case res of
    Left err -> lift $ print err
    Right r ->  lift $ print (text "steps results" $$ vcat (map disp r))
      
semiauto :: StateT Env IO ()
semiauto = do
  env <- get
  let pds = pfdecls env
      res = foldM semi env pds
  case res of
    Left err -> 
      lift $ print (disp err)
    Right env' -> do put env'
                     lift $ print (disp env')
                     lift $ print (text "automated proof reconstruction success!")
                     
    
semi :: Env -> (Name, Exp, Exp) -> Either Doc Env
semi env (n, f, pf) = 
    let ks = kinds env
        lms = map (\ (n,(_, e)) -> (n, e)) $ lemmas env
        as = axioms env
        pEnv = as ++ lms
        init = [(n, f, [([], f, (n, f):pEnv)], Nothing,0)] in
    case constrProof n init ks pf of    
      Right e -> 
        let e' = rebind e
            res' = runProofCheck n e' f env in
        case res' of
                 Left err -> Left (disp err $$ text ("fail to load file "))
                 Right _ ->             
                   Right $ extendLemma n e' f env
      Left err -> Left err
