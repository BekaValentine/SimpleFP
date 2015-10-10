{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module DependentImplicit.Core.Abstraction where

import Control.Applicative
import Control.Monad.Reader

import Abs
import Plicity
import Scope
import DependentImplicit.Core.ConSig
import DependentImplicit.Core.Term

instance Abstract a b Term => Abstract a b Pattern where
  abstract (VarPat x) = return $ VarPat x
  abstract (ConPat c ps) = ConPat c <$> abstract ps
  abstract (AssertionPat m) = AssertionPat <$> abstract m

instance Abstract a b Term => Abstract a b PatternSeq where
  abstract PatternSeqNil
    = return PatternSeqNil
  abstract (PatternSeqCons plic p sc)
    = PatternSeqCons plic <$> abstract p <*> abstractScope sc

instance Abstract a b Term => Abstract a b Clause where
  abstract (Clause ps sc)
    = Clause <$> abstract ps <*> abstractScope sc

instance Abstract a b Term => Abstract a b CaseMotive where
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
  abstract (Var (Generated i))
    = return $ Var (Generated i)
  abstract (Ann m ty)
    = Ann <$> abstract m <*> return ty
  abstract Type
    = return Type
  abstract (Fun plic a sc)
    = Fun plic <$> abstract a <*> abstractScope sc
  abstract (Lam plic sc)
    = Lam plic <$> abstractScope sc
  abstract (App plic f a)
    = App plic <$> abstract f <*> abstract a
  abstract (Con c as)
    = Con c <$> forM as (\(plic,a) -> do a' <- abstract a ; return (plic,a'))
  abstract (Case as t cs)
    = Case <$> mapM abstract as <*> abstract t <*> mapM abstract cs

instance Abstract Int Term Term where
  abstract (Meta i)
    = return $ Meta i
  abstract (Var (Name x))
    = return $ Var (Name x)
  abstract (Var (Generated i))
    = reader $ \e ->
        case lookup i e of
          Nothing -> Var (Generated i)
          Just m  -> m
  abstract (Ann m ty)
    = Ann <$> abstract m <*> return ty
  abstract Type
    = return Type
  abstract (Fun plic a sc)
    = Fun plic <$> abstract a <*> abstractScope sc
  abstract (Lam plic sc)
    = Lam plic <$> abstractScope sc
  abstract (App plic f a)
    = App plic <$> abstract f <*> abstract a
  abstract (Con c as)
    = Con c <$> forM as (\(plic,a) -> do a' <- abstract a ; return (plic,a'))
  abstract (Case as t cs)
    = Case <$> mapM abstract as <*> abstract t <*> mapM abstract cs

funHelper :: Plicity -> String -> Term -> Term -> Term
funHelper plic x a b = Fun plic a (scope [x] b)

lamHelper :: Plicity -> String -> Term -> Term
lamHelper plic x b = Lam plic (scope [x] b)

patternSeqHelper :: Plicity -> Pattern -> [String] -> PatternSeq -> PatternSeq
patternSeqHelper plic p xs ps = PatternSeqCons plic p (scope xs ps)

clauseHelper :: PatternSeq -> [String] -> Term -> Clause
clauseHelper ps xs b = Clause ps (scope xs b)

consMotiveHelper :: String -> Term -> CaseMotive -> CaseMotive
consMotiveHelper x a b = CaseMotiveCons a (scope [x] b)

instance Abstract a Term Term => Abstract a Term (ConSig Term) where
  abstract (ConSigNil a)
    = ConSigNil <$> abstract a
  abstract (ConSigCons plic a sc)
    = ConSigCons plic <$> abstract a <*> abstractScope sc

conSigHelper :: [DeclArg] -> Term -> ConSig Term
conSigHelper [] b = ConSigNil b
conSigHelper (DeclArg plic x a:as) b
  = ConSigCons plic a (scope [x] (conSigHelper as b))