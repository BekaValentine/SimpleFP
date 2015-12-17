{-# OPTIONS -Wall #-}

module Dependent.Core.Program where

import Data.List (intercalate)

import Parens
import Dependent.Core.ConSig
import Dependent.Core.Term



-- Term Declarations

data TermDeclaration
  = TermDeclaration String Term Term
  | WhereDeclaration String Term [([Pattern],[String],Term)]

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
  = TypeDeclaration String [DeclArg] [(String,ConSig Term)]

instance Show TypeDeclaration where
  show (TypeDeclaration tycon tyargs [])
    = "data " ++ tycon ++ concat (map (\x -> " " ++ show x) tyargs) ++ " end"
  show (TypeDeclaration tycon tyargs alts)
    = "data " ++ tycon ++ concat (map (\x -> " " ++ show x) tyargs) ++ " where"
   ++ concat [ "\n" ++ c ++ " : " ++ showConSig (Var . Name) sig | (c,sig) <- alts ]
   ++ "\nend"



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