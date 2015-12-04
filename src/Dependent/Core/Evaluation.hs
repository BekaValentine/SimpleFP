{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Dependent.Core.Evaluation where

import Control.Monad.Except

import Env
import Eval
import Scope
import Dependent.Core.Term



-- Pattern Matching

matchPattern :: Pattern -> Term -> Maybe [Term]
matchPattern (VarPat _) v = Just [v]
matchPattern (ConPat c ps) (Con c' as) | c == c'
  = fmap concat $ zipWithM matchPattern ps as
matchPattern (AssertionPat _) _ = Just []
matchPattern _ _ = Nothing

matchPatterns :: [Pattern] -> [Term] -> Maybe [Term]
matchPatterns [] []
  = Just []
matchPatterns (p:ps) (m:ms)
  = do vs <- matchPattern p m
       vs' <- matchPatterns ps ms
       return $ vs ++ vs'
matchPatterns _ _
  = Nothing

matchClauses :: [Clause] -> [Term] -> Maybe Term
matchClauses [] _ = Nothing
matchClauses (Clause psc sc:cs) ms
  = case matchPatterns (descope Name psc) ms of
      Nothing -> matchClauses cs ms
      Just vs -> Just (instantiate sc (removeByDummies (names psc) vs))



-- Standard Eager Evaluation

instance Eval (Environment String Term) Term where
  eval (Meta i)
    = return $ Meta i
  eval (Var (Name x))
    = do env <- environment
         case lookup x env of
           Nothing -> throwError $ "Unknown constant/defined term: " ++ x
           Just m  -> eval m
  eval (Var (Generated x i))
    = return $ Var (Generated x i)
  eval (Ann m _)
    = eval m
  eval Type
    = return Type
  eval (Fun a sc)
    = return $ Fun a sc
  eval (Lam sc)
    = return $ Lam sc
  eval (App f a)
    = do ef <- eval f
         ea <- eval a
         case ef of
           Lam sc -> eval (instantiate sc [ea])
           _      -> return $ App ef ea
  eval (Con c as)
    = do eas <- mapM eval as
         return $ Con c eas
  eval (Case ms mot cs)
    = do ems <- mapM eval ms
         case matchClauses cs ems of
           Nothing -> throwError $ "Incomplete pattern match: " ++ show (Case ms mot cs)
           Just b  -> eval b