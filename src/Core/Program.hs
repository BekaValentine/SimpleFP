module Core.Program where

import Data.List (intercalate)

import Core.Term
import Core.Type



-- Term Declarations

data TermDeclaration
  = TermDeclaration String Type Term

instance Show TermDeclaration where
  show (TermDeclaration n ty def)
    = "let " ++ n ++ " : " ++ show ty ++ " = " ++ show def ++ " end"



-- Type Declarations

data TypeDeclaration
  = TypeDeclaration String [(String,[Type])]

instance Show TypeDeclaration where
  show (TypeDeclaration tycon [])
    = "data " ++ tycon ++ " end"
  show (TypeDeclaration tycon alts)
    = "data " ++ tycon ++ " = "
   ++ intercalate " | " [ c ++ "(" ++ intercalate "," (map show args) ++ ")"
                        | (c,args) <- alts
                        ]
   ++ " end"



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