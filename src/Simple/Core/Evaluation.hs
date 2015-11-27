{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Simple.Core.Evaluation where

import Control.Monad.Except

import Env
import Eval
import Scope
import Simple.Core.Term


-- Pattern Matching

match :: Pattern -> Term -> Maybe [Term]
match (VarPat _) v = Just [v]
match (ConPat c ps) (Con c' as)
  | c == c' && length ps == length as
  = fmap concat (zipWithM match ps as)
match _ _ = Nothing

matchTerms :: [Pattern] -> [Term] -> Maybe [Term]
matchTerms ps zs = fmap concat (zipWithM match ps zs)

matchClauses :: [Clause] -> [Term] -> Maybe Term
matchClauses [] _
  = Nothing
matchClauses (Clause psc sc:cs) vs
  = case matchTerms (descope Name psc) vs of
      Nothing -> matchClauses cs vs
      Just xs -> Just (instantiate sc xs)



-- Standard Eager Evaluation

instance Eval (Environment String Term) Term where
  eval (Var (Name x))
    = do env <- environment
         case lookup x env of
           Nothing -> throwError $ "Unknown constant/defined term: " ++ x
           Just m  -> return m
  eval (Var (Generated x i))
    = return $ Var (Generated x i)
  eval (Ann m _)
    = eval m
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
  eval (Case ms cs)
    = do ems <- mapM eval ms
         case matchClauses cs ems of
           Nothing -> throwError $ "Incomplete pattern match: " ++ show (Case ms cs)
           Just b  -> eval b