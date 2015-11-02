{-# OPTIONS -Wall #-}

module Record.Core.Program where

import Data.List (intercalate)

import Record.Core.ConSig
import Record.Core.Term



-- Term Declarations

data TermDeclaration
  = TermDeclaration String Term Term

instance Show TermDeclaration where
  show (TermDeclaration n ty def)
    = "let " ++ n ++ " : " ++ show ty ++ " = " ++ show def ++ " end"



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


data Module
  = Module String [OpenSettings] [Statement]

instance Show Module where
  show (Module n [] stmts)
    = "module " ++ n ++ " where\n\n" ++ intercalate "\n\n" (map show stmts) ++ "\n\nend"
  show (Module n settings stmts)
    = "module " ++ n ++ " opening " ++ intercalate " | " (map show settings)
   ++ " where\n\n" ++ intercalate "\n\n" (map show stmts) ++ "\n\nend"

newtype Program = Program [Module]

instance Show Program where
  show (Program stmts) = intercalate "\n\n" (map show stmts)