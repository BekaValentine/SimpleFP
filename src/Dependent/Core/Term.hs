{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Dependent.Core.Term where

import Data.List (intercalate)

import Parens
import Scope



-- Used in multiple places

data DeclArg = DeclArg String Term

instance Show DeclArg where
  show (DeclArg x t) = "(" ++ x ++ " : " ++ show t ++ ")"



-- Terms

data Variable
  = Name String
  | Generated Int
  deriving (Eq)

data Term
  = Meta Int
  | Var Variable
  | Ann Term Term
  | Type
  | Fun Term (Scope Term Term)
  | Lam (Scope Term Term)
  | App Term Term
  | Con String [Term]
  | Case [Term] CaseMotive [Clause]

data CaseMotive
  = CaseMotiveNil Term
  | CaseMotiveCons Term (Scope Term CaseMotive)

data Clause
  = Clause (Scope Variable [Pattern]) (Scope Term Term)

data Pattern
  = VarPat Variable
  | ConPat String [Pattern]
  | AssertionPat Term




-- Case Motive Length

caseMotiveLength :: CaseMotive -> Int
caseMotiveLength (CaseMotiveNil _) = 0
caseMotiveLength (CaseMotiveCons _ sc)
  = 1 + caseMotiveLength (descope (Var . Name) sc)




-- Show Instances

instance Show Variable where
  show (Name x) = x
  show (Generated i) = "_" ++ show i

data PatternParenLoc = ConPatArg
  deriving (Eq)

instance ParenLoc Pattern where
  type Loc Pattern = PatternParenLoc
  parenLoc (VarPat _)       = [ConPatArg]
  parenLoc (ConPat _ _)     = []
  parenLoc (AssertionPat _) = [ConPatArg]

instance ParenRec Pattern where
  parenRec (VarPat x)
    = show x
  parenRec (ConPat c [])
    = c
  parenRec (ConPat c ps)
    = c ++ " " ++ unwords (map (parenthesize (Just ConPatArg)) ps)
  parenRec (AssertionPat m)
    = "." ++ parenthesize (Just AssertionPatArg) m

instance Show Pattern where
  show p = parenthesize Nothing p



data TermParenLoc
  = RootTerm
  | AnnLeft | AnnRight
  | FunArg | FunRet
  | LamBody | AppLeft | AppRight
  | ConArg | AssertionPatArg
  deriving (Eq)

instance ParenLoc Term where
  type Loc Term = TermParenLoc
  parenLoc (Meta _)
    = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,AppRight,ConArg,AssertionPatArg]
  parenLoc (Var _)
    = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,AppRight,ConArg,AssertionPatArg]
  parenLoc (Ann _ _)
    = [FunArg,FunRet,LamBody]
  parenLoc Type
    = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,AppRight,ConArg,AssertionPatArg]
  parenLoc (Fun _ _)
    = [FunArg,FunRet,LamBody]
  parenLoc (Lam _)
    = [FunArg,FunRet,LamBody]
  parenLoc (App _ _)
    = [FunArg,FunRet,AnnLeft,LamBody,AppLeft]
  parenLoc (Con _ [])
    = [FunArg,FunRet,AnnLeft,LamBody,AppLeft,AppRight,ConArg,AssertionPatArg]
  parenLoc (Con _ _)
    = [FunArg,FunRet,AnnLeft,LamBody]
  parenLoc (Case _ _ _)
    = [FunArg,FunRet,LamBody]

instance ParenRec Term where
  parenRec (Meta i)
    = "?" ++ show i
  parenRec (Var x)
    = show x
  parenRec (Ann m ty)
    = parenthesize (Just AnnLeft) m ++ " : " ++ parenthesize (Just AnnRight) ty
  parenRec Type
    = "Type"
  parenRec (Fun a sc)
    = "(" ++ unwords (names sc) ++ " : " ++ parenthesize (Just FunArg) a
   ++ ") -> " ++ parenthesize (Just FunRet)
                   (descope (Var . Name) sc)
  parenRec (Lam sc)
    = "\\" ++ unwords (names sc)
   ++ " -> " ++ parenthesize (Just LamBody)
                  (descope (Var . Name) sc)
  parenRec (App f a)
    = parenthesize (Just AppLeft) f ++ " " ++ parenthesize (Just AppRight) a
  parenRec (Con c [])
    = c
  parenRec (Con c as)
    = c ++ " " ++ intercalate " " (map (parenthesize (Just ConArg)) as)
  parenRec (Case ms mot cs)
    = "cases " ++ intercalate " || " (map (parenthesize Nothing) ms)
   ++ " motive " ++ show mot
   ++ " of " ++ intercalate " | " (map auxClause cs) ++ " end"
    where
      auxClause (Clause psc sc)
        = intercalate " || " (map show (descope Name psc))
          ++ " -> " ++ parenthesize Nothing
                         (descope (Var . Name) sc)
      


instance Show Term where
  show t = parenthesize Nothing t



instance Show CaseMotive where
  show (CaseMotiveNil ret) = show ret
  show (CaseMotiveCons arg sc)
    = "(" ++ unwords (names sc) ++ " : " ++ show arg ++ ") || "
   ++ show (descope (Var . Name) sc)