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
import Cegt.Typecheck

import Text.PrettyPrint
import System.Console.Haskeline

type History = [ProofState]

prover :: InputT (StateT (Exp, History, ProofState, [(Name, Kind)]) IO) (Maybe (Name, Exp, Exp))
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
                          do (_, [], (_, _, (_,_,gamma):_, m, i), kinds) <- lift get
                             let init = (g, exp, [([], exp, gamma)], m, i)
                             lift $ put (exp, [], init, kinds)
                             outputStrLn $
                               show (text "set to prove goal"<+> text g <+>text ":" <+> disp exp)
                             outputStrLn $ show (text "in the environment:" $$ disp gamma)
                             prover
                        other -> do outputStrLn $ "wrong format for the tactic goal \n" ++ show other
                                    prover
            Just input | Just rest <- stripPrefix "intros " input ->
              do let a = words rest
                 (gf, hist, st1, kinds) <- lift get
                 let st2@(_, pf, (_,newGoal, new):_, m, i) = intros st1 a
                 case m of
                   Nothing -> do
                     lift (put (gf, st1:hist, st2, kinds))
                     outputStrLn $ show (text "current goal:" $$ disp newGoal)
                     outputStrLn $ show (text "in the environment:" $$ disp new)
                     outputStrLn $ show (text "current mix proof term:" $$ disp pf)
                     prover
                   Just err -> do
                     outputStrLn $ show (text "error:" $$ disp err)
                     prover
            Just "undo" ->
              do (gf, hist, s, kinds) <- lift get
                 case hist of
                   [] -> do outputStrLn $ "cannot further undo"
                            prover
                   (h@(_,pf,(_,g,ns):_,_,_)):xs ->
                     do lift (put (gf, xs, h, kinds))
                        outputStrLn $ show (text "current goal:" $$ disp g)
                        outputStrLn $ show (text "in the environment:" $$ disp ns)
                        outputStrLn $ show (text "current mix proof term:" $$ disp pf)
                        prover
            Just "coind" ->
              do (gf, hist, s, kinds) <- lift get
                 case coind s of
                   (_,_,_,Just err, _) -> 
                     do outputStrLn $ show (disp err)
                        prover
                   s'@(_, _, (_,g,ns):_, Nothing, i) ->
                     do lift $ put (gf, s:hist, s', kinds)
                        outputStrLn $ show (text "current goal:" $$ disp g)
                        outputStrLn $ show (text "in the environment:" $$ disp ns)
                        prover

            Just input | Just rest <- stripPrefix "apply " input ->
              case parseExp rest of
                Left err -> do
                      outputStrLn (show (disp err))
                      prover
                Right big -> do
                  case flatten big of
                    ((Const n):ins) -> do 
                      (gf, hist, s@(_,_,(_,_,gamma):_, _, _), kinds) <- lift get
                      case kindList ins kinds of
                        Left err -> do outputStrLn $
                                         show ((text "kinding error:" $$ disp err))
                                       prover
                        Right _ ->  
                          case apply s n ins of
                            (_,_,_, Just err, _) ->
                              do outputStrLn $ show (disp err)
                                 prover
                            s'@(gn,pf,[], Nothing, _) ->
                              do
                                lift $ put (gf, s:hist, s', kinds)
                                outputStrLn $ show (text "Q.E.D with the proof:" $$ disp pf)
                                return $ Just (gn,rebind pf,gf)
                            s'@(_,pf,(_,g,gamma):_,Nothing,_ ) ->
                              do lift $ put (gf, s:hist, s', kinds)
                                 outputStrLn $ show (text "current goal:" $$ disp g)
                                 outputStrLn $ show (text "in the environment:" $$ disp gamma)
                                 outputStrLn $ show (text "current mix proof term:" $$ disp pf)
                                 prover
                    ((Var n):ins) -> do
                      (gf, hist, s@(_,_,(_,_,gamma):_, _,_), kinds) <- lift get
                      case kindList ins kinds of
                        Left err -> do outputStrLn $
                                         show ((text "kinding error:" $$ disp err))
                                       prover
                        Right _ ->                        
                          case apply s n ins of
                            (_,_,_,Just err, _) -> do
                              outputStrLn $ "fail to apply rule: " ++ (show n)
                              outputStrLn $ show (disp err)
                              prover
                            s'@(gn,pf,[],Nothing, _) ->
                              do
                                lift $ put (gf, s:hist, s', kinds)
                                outputStrLn $ show (text "Q.E.D with the proof:" $$ disp pf)
                                return $ Just (gn,rebind pf,gf)
                            s'@(_,pf,(_,g,gamma):_,Nothing,_) ->
                              do lift $ put (gf, s:hist, s', kinds)
                                 outputStrLn $ show (text "current goal:" $$ disp g)
                                 outputStrLn $ show (text "in the environment:" $$ disp gamma)
                                 outputStrLn $ show (text "current mix proof term:" $$ disp pf)
                                 prover
                                 
                    a -> do  outputStrLn $ "wrong input: " ++ (show a)
                             prover
            Just input | Just rest <- stripPrefix "applyh " input ->
              case parseExp rest of
                Left err -> do
                      outputStrLn (show (disp err))
                      prover
                Right big -> do
                  case flatten big of
                    ((Const n):[]) -> do 
                      (gf, hist, s@(_,_,(_,cg,gamma):_, _, _), kinds) <- lift get
                      case applyH kinds s n of
                            (_,_,_, Just err, _):[] ->
                              do outputStrLn $ show (disp err)
                                 prover
                            (s'@(gn,pf,[], Nothing, _)):[] ->
                              do
                                lift $ put (gf, s:hist, s', kinds)
                                outputStrLn $ show (text "Q.E.D with the proof:" $$ disp pf)
                                return $ Just (gn,rebind pf,gf)
                            (s'@(_,pf,(_,g,gamma):_,Nothing,_ )):[] ->
                              do lift $ put (gf, s:hist, s', kinds)
                                 outputStrLn $ show (text "current goal:" $$ disp g)
                                 outputStrLn $ show (text "in the environment:" $$ disp gamma)
                                 outputStrLn $ show (text "current mix proof term:" $$ disp pf)
                                 prover
                            _ -> do
                              outputStrLn $ show (text "ambiguous applyh" <+> disp n)
                              outputStrLn $ show (text "current goal:" $$ (nest 2 $ disp cg))
                              prover
                    ((Var n):[]) -> do
                      (gf, hist, s@(_,_,(_,cg,gamma):_, _,_), kinds) <- lift get
                      case applyH kinds s n of
                            (_,_,_,Just err, _):[] -> do
                              outputStrLn $ "fail to apply rule: " ++ (show n)
                              outputStrLn $ show (disp err)
                              prover
                            (s'@(gn,pf,[],Nothing, _)):[] ->
                              do
                                lift $ put (gf, s:hist, s', kinds)
                                outputStrLn $ show (text "Q.E.D with the proof:" $$ disp pf)
                                return $ Just (gn,rebind pf,gf)
                            (s'@(_,pf,(_,g,gamma):_,Nothing,_)):[] ->
                              do lift $ put (gf, s:hist, s', kinds)
                                 outputStrLn $ show (text "current goal:" $$ disp g)
                                 outputStrLn $ show (text "in the environment:" $$ disp gamma)
                                 outputStrLn $ show (text "current mix proof term:" $$ disp pf)
                                 prover
                            _ -> do
                              outputStrLn $ show (text "ambiguous applyh" <+> disp n)
                              outputStrLn $ show (text "current goal:" $$ (nest 2 $ disp cg))
                              prover
                                 
                                 
                    a -> do  outputStrLn $ "wrong input: " ++ (show a)
                             prover
                             
            Just input | Just rest <- stripPrefix "end" input -> return Nothing
            Just input | Just rest <- stripPrefix "use " input ->
              case parseExp rest of
                Left err -> do
                      outputStrLn (show (disp err))
                      prover
                Right big -> do
                  case flatten big of
                    ((Const n):ins) -> do 
                      (gf, hist, s@(_,_,(_,_,gamma):_, _, _), kinds) <- lift get
                      case kindList ins kinds of
                        Left err -> do outputStrLn $
                                         show ((text "kinding error:" $$ disp err))
                                       prover
                        Right _ ->  
                          case use s n ins of
                            (_, _, _, Just err, _) ->
                              do outputStrLn $ show ((text "fail to use rule:" <+> text n))
                                 outputStrLn $ show $ disp err
                                 prover
                            s'@(gn,pf,[], Nothing, _) ->
                              do
                                lift $ put (gf, s:hist, s', kinds)
                                outputStrLn $ show (text "Q.E.D with the proof:" $$ disp pf)
                                return $ Just (gn,rebind pf,gf)
                            s'@(_,pf,(_,g,gamma):_, Nothing, _ ) ->
                              do lift $ put (gf, s:hist, s', kinds)
                                 outputStrLn $ show (text "current goal:" $$ disp g)
                                 outputStrLn $ show (text "in the environment:" $$ disp gamma)
                                 outputStrLn $ show (text "current mix proof term:" $$ disp pf)
                                 prover
                    ((Var n):ins) -> do
                      (gf, hist, s@(_,_,(_,_,gamma):_, _, _), kinds) <- lift get
                      case kindList ins kinds of
                        Left err -> do outputStrLn $
                                         show ((text "kinding error:" $$ disp err))
                                       prover
                        Right _ ->                        
                          case use s n ins of
                            (_,_,_,Just err, _) ->
                              do outputStrLn $ "fail to apply rule: " ++ (show n)
                                 outputStrLn $ show (disp err)
                                 prover
                            s'@(gn,pf,[],Nothing, _) ->
                              do
                                lift $ put (gf, s:hist, s', kinds)
                                outputStrLn $ show (text "Q.E.D with the proof:" $$ disp pf)
                                return $ Just (gn,rebind pf,gf)
                            s'@(_,pf,(_,g,gamma):_, Nothing,_ ) ->
                              do lift $ put (gf, s:hist, s', kinds)
                                 outputStrLn $ show (text "current goal:" $$ disp g)
                                 outputStrLn $ show (text "in the environment:" $$ disp gamma)
                                 outputStrLn $ show (text "current mix proof term:" $$ disp pf)
                                 prover
                    a -> do  outputStrLn $ "wrong input: " ++ (show a)
                             prover

                             
            Just input -> do
              outputStrLn $ "unrecognized input "++ (show input)
              prover
