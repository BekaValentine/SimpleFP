module Simple.Core.Program where

import Data.List (intercalate)

import Parens
import Simple.Core.Term
import Simple.Core.Type



-- Term Declarations

data TermDeclaration
  = TermDeclaration String Type Term
  | WhereDeclaration String Type [([Pattern],[String],Term)]

instance Show TermDeclaration where
  show (TermDeclaration n ty def)
    = "let " ++ n ++ " : " ++ show ty ++ " = " ++ show def ++ " end"
  show (WhereDeclaration n ty preclauses)
    = "let " ++ n ++ " : " ++ show ty ++ " where "
        ++ intercalate " | " (map showPreclause preclauses)
    where
      showPreclause :: ([Pattern],[String],Term) -> String
      showPreclause (ps,_,b)
        = intercalate " || " (map (parenthesize Nothing) ps) ++ " -> " ++ show b



-- Type Declarations

data TypeDeclaration
  = TypeDeclaration String [(String,[Type])]

instance Show TypeDeclaration where
  show (TypeDeclaration tycon [])
    = "data " ++ tycon ++ " end"
  show (TypeDeclaration tycon alts)
    = "data " ++ tycon ++ " = "
   ++ intercalate " | " [ showAlt c as | (c,as) <- alts ]
   ++ " end"
   where
     showAlt :: String -> [Type] -> String
     showAlt c [] = c
     showAlt c as = c ++ " " ++ intercalate " " (map show as)



-- Programs

data Statement
  = TyDecl TypeDeclaration
  | TmDecl TermDeclaration

instance Show Statement where
  show (TyDecl td) = show td
  show (TmDecl td) = show td


newtype Program = Program [Statement]

instance Show Program where
  show (Program stmts) = intercalate "\n\n" (map show stmts)