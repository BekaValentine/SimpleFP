{-# OPTIONS -Wall #-}

module Quasiquote.Core.Program where

import Data.List (intercalate)

import Parens
import Plicity
import Quasiquote.Core.ConSig
import Quasiquote.Core.Term



-- Term Declarations

data TermDeclaration
  = TermDeclaration String Term Term
  | WhereDeclaration String Term [([Plicity],([Pattern],[String],Term))]
  | LetFamilyDeclaration String [DeclArg] Term
  | LetInstanceDeclaration (Either String (String,String)) [([Plicity],([Pattern],[String],Term))]

showPreclause :: ([Plicity],([Pattern],[String],Term)) -> String
showPreclause (plics,(ps,_,b))
  = intercalate " || " (map showPattern (zip plics ps)) ++ " -> " ++ show b

showPattern :: (Plicity,Pattern) -> String
showPattern (Expl,p) = parenthesize (Just ExplConPatArg) p
showPattern (Impl,p) = parenthesize (Just ImplConPatArg) p

instance Show TermDeclaration where
  show (TermDeclaration n ty def)
    = "let " ++ n ++ " : " ++ show ty ++ " = " ++ show def ++ " end"
  show (WhereDeclaration n ty preclauses)
    = "let " ++ n ++ " : " ++ show ty ++ " where "
        ++ intercalate " | " (map showPreclause preclauses)
  show (LetFamilyDeclaration n args ty)
    = "let family " ++ n ++ " " ++ unwords (map show args) ++ " : " ++ show ty ++ " end"
  show (LetInstanceDeclaration n preclauses)
    = "let instance " ++ show n ++ " where "
        ++ intercalate " | " (map showPreclause preclauses)



-- Type Declarations

data TypeDeclaration
  = TypeDeclaration String [DeclArg] [(String,ConSig Term)]
  | DataFamilyDeclaration String [DeclArg]
  | DataInstanceDeclaration Constructor [(String,ConSig Term)]

instance Show TypeDeclaration where
  show (TypeDeclaration tycon tyargs [])
    = "data " ++ tycon ++ concat (map (\x -> " " ++ show x) tyargs) ++ " end"
  show (TypeDeclaration tycon tyargs alts)
    = "data " ++ tycon ++ concat (map (\x -> " " ++ show x) tyargs) ++ " where"
   ++ concat [ "\n" ++ c ++ " : " ++ showConSig (Var . Name) sig | (c,sig) <- alts ]
   ++ "\nend"
  show (DataFamilyDeclaration tycon tyargs)
    = "data family " ++ tycon ++ concat (map (\x -> " " ++ show x) tyargs) ++ " end"
  show (DataInstanceDeclaration tycon alts)
    = "data instance " ++ show tycon ++ " where"
   ++ concat [ "\n" ++ c ++ " : " ++ showConSig (Var . Name) sig | (c,sig) <- alts ]
   ++ "\nend"



-- Programs

data Statement
  = TyDecl TypeDeclaration
  | TmDecl TermDeclaration

instance Show Statement where
  show (TyDecl td) = show td
  show (TmDecl td) = show td


data HidingUsing
  = Hiding [String]
  | Using [String]

data OpenSettings
  = OpenSettings
    { openModule :: String
    , openAs :: Maybe String
    , openHidingUsing :: Maybe HidingUsing
    , openRenaming :: [(String,String)]
    }

instance Show OpenSettings where
  show (OpenSettings m a hu r)
    = m ++ a' ++ hu' ++ r'
    where
      a' = case a of
             Nothing -> ""
             Just m' -> " as " ++ m'
      hu' = case hu of
              Nothing -> ""
              Just (Hiding ns) -> " hiding (" ++ intercalate "," ns ++ ")"
              Just (Using ns)  -> " using (" ++ intercalate "," ns ++ ")"
      r' = case r of
             [] -> ""
             _ -> " renaming (" ++ intercalate ", " [ n ++ " to " ++ n' | (n,n') <- r ] ++ ")"

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