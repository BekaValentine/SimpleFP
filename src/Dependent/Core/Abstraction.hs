{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Dependent.Core.Abstraction where

import Control.Applicative
import Control.Monad.Reader
import qualified Control.Monad.State as S

import Abs
import Scope
import Dependent.Core.ConSig
import Dependent.Core.Term



instance Abstract String Term Clause where
  abstract (Clause psc sc)
    = Clause <$> abstractScope psc <*> abstractScope sc

instance Abstract String Variable Clause where
  abstract (Clause psc sc)
    = Clause <$> abstractScope psc <*> abstractScope sc

instance Abstract String Term CaseMotive where
  abstract (CaseMotiveNil a)
    = CaseMotiveNil <$> abstract a
  abstract (CaseMotiveCons a sc)
    = CaseMotiveCons <$> abstract a <*> abstractScope sc

instance Abstract String Variable CaseMotive where
  abstract (CaseMotiveNil a)
    = CaseMotiveNil <$> abstract a
  abstract (CaseMotiveCons a sc)
    = CaseMotiveCons <$> abstract a <*> abstractScope sc

instance Abstract String Term Term where
  abstract (Meta i)
    = return $ Meta i
  abstract (Var (Name x))
    = reader $ \e ->
        case lookup x e of
          Nothing -> Var (Name x)
          Just m  -> m
  abstract (Var (Generated x i))
    = return $ Var (Generated x i)
  abstract (Ann m ty)
    = Ann <$> abstract m <*> return ty
  abstract Type
    = return Type
  abstract (Fun a sc)
    = Fun <$> abstract a <*> abstractScope sc
  abstract (Lam sc)
    = Lam <$> abstractScope sc
  abstract (App f a)
    = App <$> abstract f <*> abstract a
  abstract (Con c as)
    = Con c <$> mapM abstract as
  abstract (Case as t cs)
    = Case <$> mapM abstract as <*> abstract t <*> mapM abstract cs

instance Abstract String Variable Term where
  abstract (Meta i)
    = return $ Meta i
  abstract (Var (Name x))
    = reader $ \e ->
        case lookup x e of
          Nothing -> Var (Name x)
          Just y  -> Var y
  abstract (Var (Generated x i))
    = return $ Var (Generated x i)
  abstract (Ann m ty)
    = Ann <$> abstract m <*> return ty
  abstract Type
    = return Type
  abstract (Fun a sc)
    = Fun <$> abstract a <*> abstractScope sc
  abstract (Lam sc)
    = Lam <$> abstractScope sc
  abstract (App f a)
    = App <$> abstract f <*> abstract a
  abstract (Con c as)
    = Con c <$> mapM abstract as
  abstract (Case as t cs)
    = Case <$> mapM abstract as <*> abstract t <*> mapM abstract cs

instance Abstract String Term Pattern where
  abstract (VarPat x)
    = return $ VarPat x
  abstract (ConPat c ps)
    = ConPat c <$> mapM abstract ps
  abstract (AssertionPat m)
    = AssertionPat <$> abstract m

instance Abstract String Variable Pattern where
  abstract (VarPat (Name x))
    = reader $ \e ->
        case lookup x e of
          Nothing -> VarPat (Name x)
          Just y  -> VarPat y
  abstract (VarPat (Generated x i))
    = return $ VarPat (Generated x i)
  abstract (ConPat c ps)
    = ConPat c <$> mapM abstract ps
  abstract (AssertionPat m)
    = AssertionPat <$> abstract m

funHelper :: String -> Term -> Term -> Term
funHelper x a b = Fun a (scope [x] b)

lamHelper :: String -> Term -> Term
lamHelper x b = Lam (scope [x] b)

clauseHelper :: [Pattern] -> [String] -> Term -> Clause
clauseHelper ps xs b = Clause (scope2 xs cleanedXs cleanedPs) (scope xs b)
  where
    cleanedXs = fst (S.runState (mapM cleanXs xs) 0)
    
    cleanXs :: String -> S.State Int String
    cleanXs "_" = do i <- S.get
                     S.put (i+1)
                     return $ "$" ++ show i
    cleanXs x = return x
    
    cleanedPs = fst (S.runState (mapM cleanPs ps) 0)
    
    cleanPs :: Pattern -> S.State Int Pattern
    cleanPs (VarPat (Name "_"))
      = do i <- S.get
           S.put (i+1)
           return $ VarPat (Name ("$" ++ show i))
    cleanPs (VarPat (Name n))
      = return $ VarPat (Name n)
    cleanPs (VarPat (Generated n i))
      = return $ VarPat (Generated n i)
    cleanPs (ConPat c ps)
      = ConPat c <$> mapM cleanPs ps
    cleanPs (AssertionPat m)
      = return $ AssertionPat m

consMotiveHelper :: String -> Term -> CaseMotive -> CaseMotive
consMotiveHelper x a b = CaseMotiveCons a (scope [x] b)

instance Abstract String Term (ConSig Term) where
  abstract (ConSigNil a)
    = ConSigNil <$> abstract a
  abstract (ConSigCons a sc)
    = ConSigCons <$> abstract a <*> abstractScope sc

conSigHelper :: [DeclArg] -> Term -> ConSig Term
conSigHelper [] b = ConSigNil b
conSigHelper (DeclArg x a:as) b
  = ConSigCons a (scope [x] (conSigHelper as b))