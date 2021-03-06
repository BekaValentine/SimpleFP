{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Poly.Core.Term where

import Data.List (intercalate)

import Parens
import Scope
import Poly.Core.Type



-- Terms

data Variable
  = Name String
  | Generated String Int

data Term
  = Var Variable
  | Ann Term Type
  | Lam (Scope Term Term)
  | App Term Term
  | Con String [Term]
  | Case [Term] [Clause]

data Clause
  = Clause (Scope Variable [Pattern]) (Scope Term Term)

data Pattern
  = VarPat Variable
  | ConPat String [Pattern]



-- Show Instances

instance Show Variable where
  show (Name x) = x
  show (Generated x _) = x

data PatternParenLoc = ConPatArg
  deriving (Eq)

instance ParenLoc Pattern where
  type Loc Pattern = PatternParenLoc
  parenLoc (VarPat _)    = [ConPatArg]
  parenLoc (ConPat _ []) = [ConPatArg]
  parenLoc (ConPat _ _)  = []

instance ParenRec Pattern where
  parenRec (VarPat x)
    = show x
  parenRec (ConPat c [])
    = c
  parenRec (ConPat c ps)
    = c ++ " " ++ unwords (map (parenthesize (Just ConPatArg)) ps)


data TermParenLoc = RootTerm | AnnLeft | LamBody | AppLeft | AppRight | ConArg | CaseArg
  deriving (Eq)

instance ParenLoc Term where
  type Loc Term = TermParenLoc
  parenLoc (Var _)
    = [RootTerm,AnnLeft,LamBody,AppLeft,AppRight,ConArg,CaseArg]
  parenLoc (Ann _ _)
    = [RootTerm,LamBody,CaseArg]
  parenLoc (Lam _)
    = [RootTerm,LamBody,CaseArg]
  parenLoc (App _ _)
    = [RootTerm,AnnLeft,LamBody,AppLeft,CaseArg]
  parenLoc (Con _ [])
    = [RootTerm,AnnLeft,LamBody,AppLeft,AppRight,ConArg,CaseArg]
  parenLoc (Con _ _)
    = [RootTerm,AnnLeft,LamBody,CaseArg]
  parenLoc (Case _ _)
    = [RootTerm,LamBody]

instance ParenRec Term where
  parenRec (Var (Name x))
    = x
  parenRec (Var (Generated x _))
    = x
  parenRec (Ann m t)
    = parenthesize (Just AnnLeft) m ++ " : " ++ show t
  parenRec (Lam sc)
    = "\\" ++ unwords (names sc) ++ " -> "
   ++ parenthesize (Just LamBody)
        (descope (Var . Name) sc)
  parenRec (App f a)
    = parenthesize (Just AppLeft) f ++ " " ++ parenthesize (Just AppRight) a
  parenRec (Con c [])
    = c
  parenRec (Con c as)
    = c ++ " " ++ intercalate " " (map (parenthesize (Just ConArg)) as)
  parenRec (Case as cs)
    = "case " ++ intercalate " || " (map (parenthesize (Just CaseArg)) as) ++ " of "
   ++ intercalate " | " (map auxClause cs) ++ " end"
    where
      auxClause (Clause psc sc)
        = intercalate " || " (map (parenthesize Nothing) (descope Name psc)) ++ " -> "
       ++ parenthesize Nothing (descope (Var . Name) sc)

instance Show Term where
  show t = parenthesize Nothing t