{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module DependentImplicit.Core.Term where

import Data.List (intercalate)

import Parens
import Plicity
import Scope





-- Used in multiple places

data DeclArg
  = DeclArg Plicity String Term

instance Show DeclArg where
  show (DeclArg Expl x t) = "(" ++ x ++ " : " ++ show t ++ ")"
  show (DeclArg Impl x t) = "{" ++ x ++ " : " ++ show t ++ "}"



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
  | Fun Plicity Term (Scope Term Term)
  | Lam Plicity (Scope Term Term)
  | App Plicity Term Term
  | Con String [(Plicity, Term)]
  | Case [Term] CaseMotive [Clause]

data CaseMotive
  = CaseMotiveNil Term
  | CaseMotiveCons Term (Scope Term CaseMotive)

data Clause
  = Clause (Scope Variable [Pattern]) (Scope Term Term)

data Pattern
  = VarPat Variable
  | ConPat String [(Plicity,Pattern)]
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

data PatternParenLoc = ExplConPatArg | ImplConPatArg
  deriving (Eq)

instance ParenLoc Pattern where
  type Loc Pattern = PatternParenLoc
  parenLoc (VarPat _)       = [ExplConPatArg,ImplConPatArg]
  parenLoc (ConPat _ _)     = [ImplConPatArg]
  parenLoc (AssertionPat _) = [ExplConPatArg,ImplConPatArg]

instance ParenRec Pattern where
  parenRec (VarPat x)
    = show x
  parenRec (ConPat c [])
    = c
  parenRec (ConPat c ps)
    = c ++ " " ++ unwords (map auxConPatArg ps)
    where
      auxConPatArg :: (Plicity,Pattern) -> String
      auxConPatArg (Expl,p) = parenthesize (Just ExplConPatArg) p
      auxConPatArg (Impl,p) = "{" ++ parenthesize (Just ImplConPatArg) p ++ "}"
  parenRec (AssertionPat m)
    = "." ++ parenthesize (Just AssertionPatArg) m

instance Show Pattern where
  show p = parenthesize Nothing p



data TermParenLoc
  = RootTerm
  | AnnLeft | AnnRight
  | FunArg | FunRet
  | LamBody | AppLeft | ExplAppRight | ImplAppRight
  | ExplConArg | ImplConArg | AssertionPatArg
  deriving (Eq)

instance ParenLoc Term where
  type Loc Term = TermParenLoc
  parenLoc (Meta _)
    = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg]
  parenLoc (Var _)
    = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg]
  parenLoc (Ann _ _)
    = [FunArg,FunRet,LamBody,ImplAppRight,ImplConArg]
  parenLoc Type
    = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg]
  parenLoc (Fun _ _ _)
    = [FunArg,FunRet,LamBody,ImplAppRight,ImplConArg]
  parenLoc (Lam _ _)
    = [FunArg,FunRet,LamBody,ImplAppRight,ImplConArg]
  parenLoc (App _ _ _)
    = [FunArg,FunRet,AnnLeft,LamBody,AppLeft,ImplAppRight,ImplConArg]
  parenLoc (Con _ [])
    = [FunArg,FunRet,AnnLeft,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg]
  parenLoc (Con _ _)
    = [FunArg,FunRet,AnnLeft,LamBody,ImplAppRight,ImplConArg]
  parenLoc (Case _ _ _)
    = [FunArg,FunRet,LamBody,ImplAppRight,ImplConArg]

instance ParenRec Term where
  parenRec (Meta i)
    = "?" ++ show i
  parenRec (Var x)
    = show x
  parenRec (Ann m ty)
    = parenthesize (Just AnnLeft) m ++ " : " ++ parenthesize (Just AnnRight) ty
  parenRec Type
    = "Type"
  parenRec (Fun plic a sc)
    = let a0' = unwords (names sc) ++ " : " ++ parenthesize (Just FunArg) a
          a' = case plic of
                 Expl -> "(" ++ a0' ++ ")"
                 Impl -> "{" ++ a0' ++ "}"
      in a' ++ " -> "
      ++ parenthesize (Just FunRet)
           (descope (Var . Name) sc)
  parenRec (Lam plic sc)
    = let n0' = unwords (names sc)
          n' = case plic of
                 Expl -> n0'
                 Impl -> "{" ++ n0' ++ "}"
      in "\\" ++ n'
      ++ " -> " ++ parenthesize (Just LamBody)
                     (descope (Var . Name) sc)
  parenRec (App plic f a)
    = let a' = case plic of
                 Expl -> parenthesize (Just ExplAppRight) a
                 Impl -> "{" ++ parenthesize (Just ImplAppRight) a ++ "}"
      in parenthesize (Just AppLeft) f ++ " " ++ a'
  parenRec (Con c [])
    = c
  parenRec (Con c as)
    = let as' = [ case plic of
                    Expl -> parenthesize (Just ExplConArg) a
                    Impl -> "{" ++ parenthesize (Just ImplConArg) a ++ "}"
                | (plic,a) <- as
                ]
      in c ++ " " ++ intercalate " " as' --(map (parenthesize (Just ConArg)) as)
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