module Poly.Term where

import Data.List (intercalate)

import Poly.Type

data Term
  = Var String
  | Ann Term Type
  | Lam String Term
  | App Term Term
  | Con String [Term]
  | Case Term [Clause]

data TermParenLoc
  = RootTerm | AnnLeft
  | LamBody | AppLeft | AppRight
  | ConArg | CaseArg
  deriving (Eq)

instance Show Term where
  show t = aux RootTerm t
    where
      aux loc t
        = let (locs, str) = case t of
                Var x     -> ([RootTerm,AnnLeft,LamBody,AppLeft,AppRight,ConArg,CaseArg], x)
                Ann m t   -> ([RootTerm,LamBody,CaseArg], aux AnnLeft m ++ " : " ++ show t)
                Lam x b   -> ([RootTerm,LamBody,CaseArg], "\\" ++ x ++ " -> " ++ aux LamBody b)
                App f a   -> ([RootTerm,AnnLeft,LamBody,AppLeft,CaseArg], aux AppLeft f ++ " " ++ aux AppRight a)
                Con c []  -> ([RootTerm,AnnLeft,LamBody,AppLeft,AppRight,ConArg,CaseArg], c)
                Con c as  -> ([RootTerm,AnnLeft,LamBody,CaseArg], c ++ " " ++ intercalate " " (map (aux ConArg) as))
                Case m cs -> ([RootTerm,LamBody], "case " ++ aux CaseArg m ++ " of " ++ intercalate " | " (map show cs) ++ " end")
          in if loc `elem` locs
             then str
             else "(" ++ str ++ ")"

data Clause
  = Clause Pattern Term

instance Show Clause where
  show (Clause p t) = show p ++ " -> " ++ show t


data Pattern
  = VarPat String
  | ConPat String [Pattern]

data PatternParenLoc = RootPattern | ConPatArg
  deriving (Eq)

instance Show Pattern where
  show t = aux RootPattern t
    where
      aux c t
        = let (cs,str) = case t of
                VarPat x    -> ([RootPattern,ConPatArg], x)
                ConPat c [] -> ([RootPattern,ConPatArg], c)
                ConPat c as -> ([RootPattern], c ++ " " ++ intercalate " " (map (aux ConPatArg) as))
          in if c `elem` cs
             then str
             else "(" ++ str ++ ")"