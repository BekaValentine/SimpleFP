{-# OPTIONS -Wall #-}

module Dependent.Core.Program where

import Data.List (intercalate)

import Dependent.Core.Term



-- Term Declarations

data TermDeclaration
  = TermDeclaration String Term Term

instance Show TermDeclaration where
  show (TermDeclaration n ty def)
    = "let " ++ n ++ " : " ++ show ty ++ " = " ++ show def ++ " end"



-- Type Declarations

data TypeDeclaration
  = TypeDeclaration String [DeclArg] [(String,[DeclArg],Term)]

instance Show TypeDeclaration where
  show (TypeDeclaration tycon tyargs [])
    = "data " ++ tycon ++ concat (map (\x -> " " ++ show x) tyargs) ++ " end"
  show (TypeDeclaration tycon tyargs alts)
    = "data " ++ tycon ++ concat (map (\x -> " " ++ show x) tyargs) ++ " where"
   ++ concat [ "\n" ++ showAlt c as t | (c,as,t) <- alts ]
   ++ "\nend"
   where
     showAlt :: String -> [DeclArg] -> Term -> String
     showAlt c [] t = c ++ " : " ++ show t
     showAlt c as t = c ++ " " ++ intercalate " " (map show as) ++ " : " ++ show t



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