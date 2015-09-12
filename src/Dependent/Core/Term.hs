{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Dependent.Core.Term where

import Control.Monad.State
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
  | Case Term [Clause]
  | Cases [Term] CasesArgType [SeqClause]

data Clause
  = Clause Pattern (Scope Term Term)

data CasesArgType
  = CasesArgNil Term
  | CasesArgCons Term (Scope Term CasesArgType)

data SeqClause
  = SeqClause [Pattern] (Scope Term Term)

data Pattern
  = VarPat
  | ConPat String [Pattern]
  deriving (Eq)



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

data TermParenLoc
  = RootTerm
  | AnnLeft | AnnRight
  | FunArg | FunRet
  | LamBody | AppLeft | AppRight
  | ConArg
  deriving (Eq)

instance ParenLoc Term where
  type Loc Term = TermParenLoc
  parenLoc (Meta _)
    = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,AppRight,ConArg]
  parenLoc (Var _)
    = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,AppRight,ConArg]
  parenLoc (Ann _ _)
    = [FunArg,FunRet,LamBody]
  parenLoc Type
    = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,AppRight,ConArg]
  parenLoc (Fun _ _)
    = [FunArg,FunRet,LamBody]
  parenLoc (Lam _)
    = [FunArg,FunRet,LamBody]
  parenLoc (App _ _)
    = [FunArg,FunRet,AnnLeft,LamBody,AppLeft]
  parenLoc (Con _ [])
    = [FunArg,FunRet,AnnLeft,LamBody,AppLeft,AppRight,ConArg]
  parenLoc (Con _ _)
    = [FunArg,FunRet,AnnLeft,LamBody]
  parenLoc (Case _ _)
    = [FunArg,FunRet,LamBody]
  parenLoc (Cases _ _ _)
    = [FunArg,FunRet,LamBody]

instance ParenRec (State Int) Term where
  parenRec (Meta i)
    = return $ "?" ++ show i
  parenRec (Var x)
    = return $ show x
  parenRec (Ann m ty)
    = do m' <- parenthesize (Just AnnLeft) m
         ty' <- parenthesize (Just AnnRight) ty
         return $ m' ++ " : " ++ ty'
  parenRec Type
    = return "Type"
  parenRec (Fun a sc)
    = do i <- next
         let x = Generated i
         a' <- parenthesize (Just FunArg) a
         b' <- parenthesize (Just FunRet) (instantiate sc [Var x])
         return $ "(" ++ show x ++ " : " ++ a' ++ ") -> " ++ b'
  parenRec (Lam sc)
    = do i <- next
         let x = Generated i
         b' <- parenthesize (Just LamBody) (instantiate sc [Var x])
         return $ "\\" ++ show x ++ " -> " ++ b'
  parenRec (App f a)
    = do f' <- parenthesize (Just AppLeft) f
         a' <- parenthesize (Just AppRight) a
         return $ f' ++ " " ++ a'
  parenRec (Con c [])
    = return c
  parenRec (Con c as)
    = do as' <- mapM (parenthesize (Just ConArg)) as
         return $ c ++ " " ++ intercalate " " as'
  parenRec (Case m cs)
    = do m' <- parenthesize Nothing m
         cs' <- mapM auxClause cs
         return $ "case " ++ m' ++ " of " ++ intercalate " | " cs' ++ " end"
    where
      auxClause (Clause p sc)
        = do (pat,is) <- parenthesizeBound Nothing p
             b' <- parenthesize Nothing
                    (instantiate sc (map (Var . Generated) is))
             return $ pat ++ " -> " ++ b'
  parenRec (Cases ms ts cs)
    = do ms' <- mapM (parenthesize Nothing) ms
         let ms'' = intercalate " || " ms'
         ts' <- auxArgType ts
         cs' <- mapM auxClause cs
         return $ "cases " ++ ms'' ++ " :: " ++ ts' ++ " of " ++ intercalate " | " cs' ++ "end"
    where
      auxArgType (CasesArgNil a)
        = parenthesize Nothing a
      auxArgType (CasesArgCons a sc)
        = do a' <- parenthesize Nothing a
             i <- next
             let x = Generated i
             b' <- auxArgType (instantiate sc [Var x])
             return $ "(" ++ show x ++ " : " ++ a' ++ ") || " ++ b'
      
      auxClause (SeqClause ps sc)
        = do ps' <- mapM (parenthesizeBound Nothing) ps
             let (pats,iss) = unzip ps'
                 patseq = intercalate " || " pats
                 is = map (Var . Generated) (concat iss)
             b' <- parenthesize Nothing (instantiate sc is)
             return $ patseq ++ " -> " ++ b'
      


instance Show Term where
  show t = fst (runState (parenthesize Nothing t) (0 :: Int))