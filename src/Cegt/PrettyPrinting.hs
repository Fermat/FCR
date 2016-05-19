{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Cegt.PrettyPrinting where
import Cegt.Syntax
-- import Cegt.Rewrite
import Text.PrettyPrint
import Text.Parsec.Pos
import Data.Char
import Text.Parsec.Error(ParseError,showErrorMessages,errorPos,errorMessages)

class Disp d where
  disp :: d -> Doc
  precedence :: d -> Int
  precedence _ = 0
  
instance Disp Doc where
  disp = id

instance Disp String where
  disp x = if (isUpper $ head x) || (isLower $ head x)
           then text x
           else if head x == '`'
                then text x
                else parens $ text x

instance Disp Int where
  disp = integer . toInteger

dParen:: (Disp a) => Int -> a -> Doc
dParen level x =
   if level >= (precedence x)
   then parens $ disp x 
   else disp x

instance Disp Kind where
  disp (KVar x) = disp x
  disp Star = text "*"
  disp Formula = text "o"
  disp (a@(KArrow t1 t2)) =
    dParen (precedence a) t1
    <+> text "=>"
    <+> dParen (precedence a - 1) t2

  precedence (KArrow _ _) = 4
  precedence (KVar _) = 12

instance Disp Exp where
  disp (Const x) = disp x
  disp (Var x) = disp x
  disp (s@(App s1 s2)) =
    dParen (precedence s - 1) s1 <+>
    dParen (precedence s) s2
  disp (Lambda x t) = text "\\" <+> text x
                      <+> text "." <+> disp t
          
  disp (a@(Arrow t1 t2)) =
    disp t1
    <+> text "~>"
    <+> disp t2

  disp (a@(Forall x f)) =
    text "forall" <+> disp x
    <+> text "."
    <+> disp f

  disp (a@(Imply t1 t2)) =
    dParen (precedence a) t1
    <+> text "=>"
    <+> dParen (precedence a - 1) t2

  precedence (Imply _ _) = 4
  precedence (Var _) = 12
  precedence (Const _) = 12
  precedence (App _ _) = 10
  precedence _ = 0

instance Disp Tactic where
  disp (Intros xs) = text "intros" <+> (hcat $ map text xs)
  disp (Use n ns) = text "use" <+> disp n <+> (hsep $ map (\ y -> parens $ disp y) ns)
  disp (Apply n ns) = text "apply" <+> disp n <+> (hsep $ map (\ y -> parens $ disp y) ns)
  disp Coind = text "coind"

instance Disp [(Name, Exp)] where
  disp decl = vcat (map (\ (n, exp) -> disp n <+> text ":" <+> disp exp) decl)


-- instance Disp Decl where
--   disp (Rule n r) = disp n <+> text ":" <+> disp r

instance Disp SourcePos where
  disp sp =  text (sourceName sp) <> colon <> int (sourceLine sp)
             <> colon <> int (sourceColumn sp) <> colon

instance Disp ParseError where
 disp pe = (disp (errorPos pe)) $$
           (text "Parse Error:" $$ sem)
  where sem = text $ showErrorMessages "or" "unknown parse error"
              "expecting" "unexpected" "end of input"
              (errorMessages pe)


