{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Dependent.Core.Abstraction where

import Control.Applicative
import Control.Monad.Reader

import Abs
import Scope
import Dependent.Core.ConSig
import Dependent.Core.Term



instance Abstract String Term Pattern where
  abstract (VarPat x) = return $ VarPat x
  abstract (ConPat c ps) = ConPat c <$> abstract ps
  abstract (AssertionPat m) = AssertionPat <$> abstract m

instance Abstract String Term PatternSeq where
  abstract PatternSeqNil
    = return PatternSeqNil
  abstract (PatternSeqCons p sc)
    = PatternSeqCons <$> abstract p <*> abstractScope sc

instance Abstract String Term Clause where
  abstract (Clause ps sc)
    = Clause <$> abstract ps <*> abstractScope sc

instance Abstract String Term CaseMotive where
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

funHelper :: String -> Term -> Term -> Term
funHelper x a b = Fun a (scope [x] b)--(Scope [x] $ \[x'] -> runReader (abstract b) [(x,x')])

lamHelper :: String -> Term -> Term
lamHelper x b = Lam (scope [x] b) --(Scope [x] $ \[a] -> runReader (abstract b) [(x,a)])

patternSeqHelper :: Pattern -> [String] -> PatternSeq -> PatternSeq
patternSeqHelper p xs ps = PatternSeqCons p (scope xs ps)--(Scope xs $ \as -> runReader (abstract ps) (zip xs as))

clauseHelper :: PatternSeq -> [String] -> Term -> Clause
clauseHelper ps xs b = Clause ps (scope xs b) --(Scope xs $ \as -> runReader (abstract b) (zip xs as))

consMotiveHelper :: String -> Term -> CaseMotive -> CaseMotive
consMotiveHelper x a b = CaseMotiveCons a (scope [x] b) --(Scope [x] $ \[x'] -> runReader (abstract b) [(x,x')])

instance Abstract String Term (ConSig Term) where
  abstract (ConSigNil a)
    = ConSigNil <$> abstract a
  abstract (ConSigCons a sc)
    = ConSigCons <$> abstract a <*> abstractScope sc

conSigHelper :: [DeclArg] -> Term -> ConSig Term
conSigHelper [] b = ConSigNil b
conSigHelper (DeclArg x a:as) b
  = ConSigCons a (scope [x] (conSigHelper as b)) --(Scope [x] $ \[v] -> runReader (abstract (conSigHelper as b)) [(x,v)])