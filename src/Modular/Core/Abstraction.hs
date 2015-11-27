{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Modular.Core.Abstraction where

import Control.Applicative
import Control.Monad.Reader

import Abs
import Plicity
import Scope
import Modular.Core.ConSig
import Modular.Core.Term

instance Abstract a b c => Abstract a b (Plicity,c) where
  abstract (plic,x) = (,) plic <$> abstract x

instance (Abstract a b Pattern, Abstract a b Term) => Abstract a b Clause where
  abstract (Clause psc sc)
    = Clause <$> abstractScope psc <*> abstractScope sc

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
  abstract (Var (Generated x i))
    = return $ Var (Generated x i)
  abstract (DottedVar m var)
    = return $ DottedVar m var
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
  abstract (OpenIn settings m)
    = OpenIn settings <$> abstract m

instance Abstract Int Term Term where
  abstract (Meta i)
    = return $ Meta i
  abstract (Var (Name x))
    = return $ Var (Name x)
  abstract (Var (Generated x i))
    = reader $ \e ->
        case lookup i e of
          Nothing -> Var (Generated x i)
          Just m  -> m
  abstract (DottedVar m var)
    = return $ DottedVar m var
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
  abstract (OpenIn settings m)
    = OpenIn settings <$> abstract m

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
  abstract (DottedVar m var)
    = return $ DottedVar m var
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
  abstract (OpenIn settings m)
    = OpenIn settings <$> abstract m

instance Abstract Int Variable Term where
  abstract (Meta i)
    = return $ Meta i
  abstract (Var (Name x))
    = return $ Var (Name x)
  abstract (Var (Generated x i))
    = reader $ \e ->
        case lookup i e of
          Nothing -> Var (Generated x i)
          Just y  -> Var y
  abstract (DottedVar m var)
    = return $ DottedVar m var
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
  abstract (OpenIn settings m)
    = OpenIn settings <$> abstract m

instance Abstract String Term Pattern where
  abstract (VarPat x)
    = return $ VarPat x
  abstract (ConPat c ps)
    = ConPat c <$> mapM abstract ps
  abstract (AssertionPat m)
    = AssertionPat <$> abstract m

instance Abstract Int Term Pattern where
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

instance Abstract Int Variable Pattern where
  abstract (VarPat (Name x))
    = return $ VarPat (Name x)
  abstract (VarPat (Generated x i))
    = reader $ \e ->
        case lookup i e of
          Nothing -> VarPat (Generated x i)
          Just y  -> VarPat y
  abstract (ConPat c ps)
    = ConPat c <$> mapM abstract ps
  abstract (AssertionPat m)
    = AssertionPat <$> abstract m

funHelper :: Plicity -> String -> Term -> Term -> Term
funHelper plic x a b = Fun plic a (scope [x] b)

lamHelper :: Plicity -> String -> Term -> Term
lamHelper plic x b = Lam plic (scope [x] b)

clauseHelper :: [Pattern] -> [String] -> Term -> Clause
clauseHelper ps xs b = Clause (scope xs ps) (scope xs b)

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