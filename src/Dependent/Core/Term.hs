{-# OPTIONS -Wall #-}

module Dependent.Core.Term where

import Data.List (intercalate)



-- Used in multiple places

newtype DeclArg = DeclArg (String,Term)

instance Show DeclArg where
  show (DeclArg (x,t)) = "(" ++ x ++ " : " ++ show t ++ ")"



-- Terms

data Term
  = Meta Int
  | Var String
  | Ann Term Term
  | Type
  | Fun String Term Term
  | Lam String Term
  | App Term Term
  | Con String [Term]
  | Case CaseArgSequence [Clause]

data TermParenLoc
  = RootTerm
  | AnnLeft | AnnRight
  | FunArg | FunRet
  | LamBody | AppLeft | AppRight
  | ConArg
  deriving (Eq)

instance Show Term where
  show tm = aux RootTerm tm
    where
      aux loc t
        = let (locs, str) = case t of
                Meta i    -> ([RootTerm,AnnLeft,FunArg,FunRet,LamBody,AppLeft,AppRight,ConArg], "?" ++ show i)
                Var x     -> ([RootTerm,AnnLeft,FunArg,FunRet,LamBody,AppLeft,AppRight,ConArg], x)
                Ann m ty  -> ([RootTerm,FunArg,LamBody], aux AnnLeft m ++ " : " ++ show ty)
                Type      -> ([RootTerm,AnnLeft,FunArg,FunRet,LamBody,AppLeft,AppRight,ConArg], "Type")
                Fun x a b -> ([RootTerm,FunArg,FunRet,LamBody], "(" ++ x ++ " : " ++ aux FunArg a ++ ") -> " ++ aux FunRet b)
                Lam x b   -> ([RootTerm,FunArg,FunRet,LamBody], "\\" ++ x ++ " -> " ++ aux LamBody b)
                App f a   -> ([RootTerm,FunArg,FunRet,AnnLeft,LamBody,AppLeft], aux AppLeft f ++ " " ++ aux AppRight a)
                Con c []  -> ([RootTerm,FunArg,FunRet,AnnLeft,LamBody,AppLeft,AppRight,ConArg], c)
                Con c as  -> ([RootTerm,FunArg,FunRet,AnnLeft,LamBody], c ++ " " ++ intercalate " " (map (aux ConArg) as))
                Case m cs -> ([RootTerm,FunArg,FunRet,LamBody], "case " ++ show m ++ " of " ++ intercalate " | " (map show cs) ++ " end")
          in if loc `elem` locs
             then str
             else "(" ++ str ++ ")"

newtype CaseArgSequence = CaseArgSequence [Term]

instance Show CaseArgSequence where
  show (CaseArgSequence ms0) = go ms0
    where
      go [] = "<empty case args>"
      go [m] = show m
      go (m:ms) = show m ++ " || " ++ go ms

data Clause
  = Clause PatternSequence Term

instance Show Clause where
  show (Clause p t) = show p ++ " -> " ++ show t

newtype PatternSequence = PatternSequence [Pattern]

instance Show PatternSequence where
  show (PatternSequence ps0) = go ps0
    where
      go [] = "<empty pattern>"
      go [p] = show p
      go (p:ps) = show p ++ " || " ++ go ps

data Pattern
  = VarPat String
  | ConPat String [Pattern]

data PatternParenLoc = RootPattern | ConPatArg
  deriving (Eq)

instance Show Pattern where
  show tm = aux RootPattern tm
    where
      aux loc t
        = let (locs,str) = case t of
                VarPat x    -> ([RootPattern,ConPatArg], x)
                ConPat c [] -> ([RootPattern,ConPatArg], c)
                ConPat c as -> ([RootPattern], c ++ " " ++ intercalate " " (map (aux ConPatArg) as))
          in if loc `elem` locs
             then str
             else "(" ++ str ++ ")"