module Cegt.Interaction where
import Cegt.Syntax
import Cegt.Rewrite

normalize :: Exp -> Exp
normalize (Var a) = Var a
normalize Star = Star
normalize (Const a) = Const a
normalize (Lambda x t) = Lambda x (normalize t)
normalize (App (Lambda x t') t) = applyE [(x, t)] t'
normalize (App (Var x) t) = App (Var x) (normalize t)
normalize (App (Const x) t) = App (Const x) (normalize t)
normalize (App t' t) = normalize (App (normalize t') (normalize t))
normalize (Imply t t') = Imply (normalize t) (normalize t')
normalize (Forall x t) = Forall x (normalize t)

quantify :: Exp -> ([Name], Exp)
quantify a@(Arrow t t') = ("p":(free a), Imply (App (Var "p") t') (App (Var "p") t))

apply :: Exp -> [(Name, Exp)] -> Name -> [Exp] -> Maybe Exp
apply goal env k ins = case lookup k env of
                           Nothing -> Nothing
                           Just (Arrow t t') -> let (xs, Imply e e') = quantify $ Arrow t t'
                                                    sub = zip xs ins
                                                    body = normalize $ applyE sub e
                                                    head = normalize $ applyE sub e'
                                                in if head == goal then Just body
                                                   else Nothing

resolve :: Exp -> [(Name, Exp)] -> Name -> Maybe Exp
resolve goal env k = case lookup k env of
                           Nothing -> Nothing
                           Just (Arrow t t') ->
                             let (xs, Imply e e') = quantify $ Arrow t t'
                                 instCxt = [(p, s) | (p, e) <- getSubterms goal, s <- match t e, s /= []]
                             in case instCxt of
                               [] -> Nothing
                               (p,ins):xs ->
                                 let
                                   cxt = Lambda "y" (replace e p (Var "y"))
                                   sub = zip xs (cxt:ins) 
                                   body = normalize $ applyE sub e
                                   head = normalize $ applyE sub e'
                                 in Just body
                                    
                 
                                                    
