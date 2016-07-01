{-# LANGUAGE  ScopedTypeVariables, PatternGuards, StandaloneDeriving, DeriveDataTypeable #-}
module Main where
import IProver
import Fcr.Parser
import Fcr.Guardness
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
main = evalStateT (runInputT defaultSettings loop) emptyEnv
  where
    loop :: InputT (StateT Env IO) ()
    loop = do
      minput <- getInputLine "fcr> "
      case minput of
        Nothing -> return ()
        Just ":q" -> return ()
        Just ":env" -> do
          env <- lift get
          outputStrLn $ show (text "the current environment" $$ disp env)
--          outputStrLn $ show (rules env)
          loop
        Just ":iprover" -> do
          env <- lift get
          let gamma = axioms env ++ map (\ (x,(_,y))-> (x,y)) (lemmas env)
              ks = kinds env
          result <- lift $ lift $ evalStateT (runInputT defaultSettings prover)
                    (Var "dummy", [], ("dummy", Var "dummy", [([],Var "dummy" ,gamma)], Nothing, 0), ks)
          case result of
            Nothing -> loop
            Just (n, p, f) -> 
              case runProofCheck n p f env of
                Left err ->
                  outputStrLn (show (disp err)) >> loop
                Right _ -> lift (modify (extendLemma n p f)) >> loop
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
                                 res = getTrace (rules state) e num
                             outputStrLn $ "the execution trace is:\n " ++ (show $ disp res)
                             loop
                _ -> do outputStrLn $ "not enough argument for :outer \n"
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
                                 res = getTrace' (rules state) e num
                             outputStrLn $ "the execution trace is:\n " ++ (show $ disp res)
                             loop
                _ -> do outputStrLn $ "not enough argument for :inner \n"
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
                                 redTree = reduce (rules state) ([], "_", e) num
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
                                 res = getTrace' (rules state) e num
                                 pf = partial res
                             outputStrLn $ show (text "the execution trace is:" $$ disp res)
                             outputStrLn $ show (text "the partial proof is:" $$ disp pf)
                             loop
                _ -> do outputStrLn $ "not enough argument for :partial\n"
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
                                 res = getTrace' (rules state) e num
                                 pf = constrLoop res
                             outputStrLn $ "the execution trace is:\n " ++ (show $ disp res)
                             case pf of
                               [] -> do outputStrLn $ "fail to construct proof.\n "
                                        loop
                               (n1,e1):(n2,e2):[] -> do
                                 outputStrLn $ show (text "the proof is" $$ (text n1 <+> text "=" <+>disp e1 $$ (text n2 <+> text "=" <+>disp e2)))
                                 
                                 loop
                _ -> do outputStrLn $ "not enough argument for :loop "
                        loop
                   | Just rest <- stripPrefix ":l " input ->
              do let filename:[] = words rest
                 lift (put emptyEnv)
                 lift (loadFile filename)
                 loop
                   | otherwise -> do outputStrLn $ "Unrecognize input : " ++ input
                                     loop



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
                                                    let pds = pfdecls env'
                                                        r = mapM (\ (x, y, z) -> checkG x z) pds
                                                    case r of
                                                      Left err ->
                                                        lift $ print
                                                        (disp err $$ text "fail to load file")
                                                      Right _ -> do
                                                        lift $ print
                                                          (text "pass the guardness check")
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



checkG :: Name -> Exp -> Either Doc ()
checkG n e = if guardness n e then return ()
             else Left $ text "unguarded definition: " $$ (text n <+> text "=" $$ disp e)

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
      res = foldM (\ x y -> semi x y) env pds
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

