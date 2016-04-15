{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module PrettyPrinting where
import Syntax

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

instance Disp Exp where
  disp (Const x) = disp x
  disp (Constr x) = disp x
  disp (Var x) = disp x
  disp (s@(App s1 s2)) =
    dParen (precedence s - 1) s1 <+>
    dParen (precedence s) s2
  disp (Lambda x t) = text "\\" <+> text x
                      <+> text "." <+> disp t
          
  disp (Pos _ t) = disp t
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

  precedence (Pos _ t) = precedence t
  precedence (Var _) = 12
  precedence (Constr _) = 12
  precedence (Const _) = 12
  precedence (App _ _) = 10
  precedence _ = 0


instance Disp Module where
  disp (Module decl) = vcat (map disp decl)

instance Disp Decl where
  disp (Rule n r) = disp n <+> text ":" <+> disp r

instance Disp SourcePos where
  disp sp =  text (sourceName sp) <> colon <> int (sourceLine sp)
             <> colon <> int (sourceColumn sp) <> colon

instance Disp ParseError where
 disp pe = (disp (errorPos pe)) $$
           (text "Parse Error:" $$ sem)
  where sem = text $ showErrorMessages "or" "unknown parse error"
              "expecting" "unexpected" "end of input"
              (errorMessages pe)

