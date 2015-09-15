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
  | Generated Int

data Term
  = Var Variable
  | Ann Term Type
  | Lam (Scope Term Term)
  | App Term Term
  | Con String [Term]
  | Case Term [Clause]

data Clause
  = Clause Pattern (Scope Term Term)

data Pattern
  = VarPat
  | ConPat String [Pattern]



-- Show Instances

instance Show Variable where
  show (Name x) = x
  show (Generated i) = "_" ++ show i

data PatternParenLoc = ConPatArg
  deriving (Eq)

instance ParenLoc Pattern where
  type Loc Pattern = PatternParenLoc
  parenLoc VarPat        = [ConPatArg]
  parenLoc (ConPat _ []) = [ConPatArg]
  parenLoc (ConPat _ _)  = []

instance ParenBound Pattern where
  parenBound VarPat
    = nextName
  parenBound (ConPat c [])
    = return c
  parenBound (ConPat c ps)
    = do ps' <- mapM (parenthesizeBound (Just ConPatArg)) ps
         return $ c ++ " " ++ unwords ps'


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
  parenRec (Var (Generated i))
    = "_" ++ show i
  parenRec (Ann m t)
    = parenthesize (Just AnnLeft) m ++ " : " ++ show t
  parenRec (Lam sc)
    = "\\" ++ unwords (names sc) ++ " -> "
   ++ parenthesize (Just LamBody)
        (instantiate sc [ Var (Name x) | x <- names sc ])
  parenRec (App f a)
    = parenthesize (Just AppLeft) f ++ " " ++ parenthesize (Just AppRight) a
  parenRec (Con c [])
    = c
  parenRec (Con c as)
    = c ++ " " ++ intercalate " " (map (parenthesize (Just ConArg)) as)
  parenRec (Case a cs)
    = "case " ++ parenthesize (Just CaseArg) a ++ " of "
   ++ intercalate " | " (map auxClause cs) ++ " end"
    where
      auxClause (Clause p sc)
        = parenthesizeBoundAtNames Nothing p (names sc) ++ " -> "
       ++ parenthesize Nothing (instantiate sc [ Var (Name x) | x <- names sc ])

instance Show Term where
  show t = parenthesize Nothing t