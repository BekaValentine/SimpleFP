{-# OPTIONS -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Dependent.Core.Evaluation where

import Control.Monad (guard,zipWithM)

import Eval
import Scope
import Dependent.Core.Term



-- Pattern Matching

match :: Pattern -> Term -> Maybe [Term]
match VarPat v = Just [v]
match (ConPat c ps) (Con c' as) | c == c' && length ps == length as
  = do vss <- zipWithM match ps as
       return $ concat vss
match _ _ = Nothing

matchSequence :: [Pattern] -> [Term] -> Maybe [Term]
matchSequence ps ms
  = do guard $ length ps == length ms
       vss <- zipWithM match ps ms
       return $ concat vss

matchClauses :: [Clause] -> Term -> Maybe Term
matchClauses [] _ = Nothing
matchClauses (Clause p sc:cs) m
  = case match p m of
      Nothing -> matchClauses cs m
      Just vs -> Just (instantiate sc vs)

matchSeqClauses :: [SeqClause] -> [Term] -> Maybe Term
matchSeqClauses [] _ = Nothing
matchSeqClauses (SeqClause ps sc:cs) ms
  = case matchSequence ps ms of
      Nothing -> matchSeqClauses cs ms
      Just vs -> Just (instantiate sc vs)



-- Standard Eager Evaluation

instance Eval Term Term where
  eval (Meta i)
    = return $ Meta i
  eval (Var (Name x))
    = do env <- environment
         case lookup x env of
           Nothing -> throw ("Unbound variable: " ++ x ++ "\nEnvironment: " ++ show env)
           Just m  -> return m
  eval (Var (Generated i))
    = return $ Var (Generated i)
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
  eval (Case m cs)
    = do em <- eval m
         case matchClauses cs em of
           Nothing -> throw $ "Incomplete pattern match: " ++ show (Case m cs)
           Just b  -> eval b
  eval (Cases ms t cs)
    = do ems <- mapM eval ms
         case matchSeqClauses cs ems of
           Nothing -> throw $ "Incomplete pattern match: " ++ show (Cases ms t cs)
           Just b  -> eval b