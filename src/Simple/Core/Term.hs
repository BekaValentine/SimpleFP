{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Simple.Core.Term where

import Control.Monad.State
import Data.List (intercalate)

import Parens
import Scope
import Simple.Core.Type



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

next :: State Int Int
next = do i <- get
          put (i+1)
          return i

data PatternParenLoc = ConPatArg
  deriving (Eq)

instance ParenLoc Pattern where
  type Loc Pattern = PatternParenLoc
  parenLoc VarPat        = [ConPatArg]
  parenLoc (ConPat _ []) = [ConPatArg]
  parenLoc (ConPat _ _)  = []

instance ParenBound (State Int) Pattern where
  parenBound VarPat
    = do i <- next
         return (show (Generated i),[i])
  parenBound (ConPat c [])
    = return (c,[])
  parenBound (ConPat c ps)
    = do r <- mapM (parenthesizeBound (Just ConPatArg)) ps
         let (ps',xs) = unzip r
         return (c ++ " " ++ intercalate " " ps', concat xs)


data TermParenLoc = AnnLeft | LamBody | AppLeft | AppRight | ConArg | CaseArg
  deriving (Eq)

instance ParenLoc Term where
  type Loc Term = TermParenLoc
  parenLoc (Var _)
    = [AnnLeft,LamBody,AppLeft,AppRight,ConArg,CaseArg]
  parenLoc (Ann _ _)
    = [LamBody,CaseArg]
  parenLoc (Lam _)
    = [LamBody,CaseArg]
  parenLoc (App _ _)
    = [AnnLeft,LamBody,AppLeft,CaseArg]
  parenLoc (Con _ [])
    = [AnnLeft,LamBody,AppLeft,AppRight,ConArg,CaseArg]
  parenLoc (Con _ _)
    = [AnnLeft,LamBody,CaseArg]
  parenLoc (Case _ _)
    = [LamBody]

instance ParenRec (State Int) Term where
  parenRec (Var (Name x))
    = return x
  parenRec (Var (Generated i))
    = return $ "_" ++ show i
  parenRec (Ann m t)
    = do m' <- parenthesize (Just AnnLeft) m
         return $ m' ++ " : " ++ show t
  parenRec (Lam sc)
    = do i <- next
         b' <- parenthesize (Just LamBody)
                 (instantiate sc [Var (Generated i)])
         return $ "\\" ++ show i ++ " -> " ++ b'
  parenRec (App f a)
    = do f' <- parenthesize (Just AppLeft) f
         a' <- parenthesize (Just AppRight) a
         return $ f' ++ " " ++ a'
  parenRec (Con c [])
    = return c
  parenRec (Con c as)
    = do as' <- mapM (parenthesize (Just ConArg)) as
         return $ c ++ " " ++ intercalate " " as'
  parenRec (Case a cs)
    = do a' <- parenthesize (Just CaseArg) a
         cs' <- mapM auxClause cs
         return $ "case " ++ a' ++ " of " ++ intercalate " | " cs' ++ "end"
    where
      auxClause (Clause p sc)
        = do (pat,is) <- parenthesizeBound Nothing p
             b' <- parenthesize Nothing
                    (instantiate sc (map (Var . Generated) is))
             return $ pat ++ " -> " ++ b'

instance Show Term where
  show t = fst (runState (parenRec t) (0 :: Int))