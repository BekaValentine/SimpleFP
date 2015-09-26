{-# OPTIONS -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Dependent.Core.Evaluation where

import Eval
import Scope
import Dependent.Core.Term



-- Pattern Matching

matchPattern :: Pattern -> Term -> Maybe [Term]
matchPattern VarPat v = Just [v]
matchPattern (ConPat c ps) (Con c' as) | c == c'
  = matchPatternSeq ps as
matchPattern (AssertionPat _) _ = Just []
matchPattern _ _ = Nothing

matchPatternSeq :: PatternSeq -> [Term] -> Maybe [Term]
matchPatternSeq PatternSeqNil []
  = Just []
matchPatternSeq (PatternSeqCons p sc) (m:ms)
  = do vs <- matchPattern p m
       vs' <- matchPatternSeq (instantiate sc [ Var (Name x) | x <- names sc ]) ms
       return $ vs ++ vs'
matchPatternSeq _ _
  = Nothing

matchClauses :: [Clause] -> [Term] -> Maybe Term
matchClauses [] _ = Nothing
matchClauses (Clause ps sc:cs) ms
  = case matchPatternSeq ps ms of
      Nothing -> matchClauses cs ms
      Just vs -> Just (instantiate sc vs)



-- Standard Eager Evaluation

instance Eval Term Term where
  eval (Meta i)
    = return $ Meta i
  eval (Var (Name x))
    = do env <- environment
         case lookup x env of
           Nothing -> throw ("Unbound variable: " ++ x ++ "\nEnvironment: " ++ show env)
           Just m  -> eval m
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
  eval (Case ms mot cs)
    = do ems <- mapM eval ms
         case matchClauses cs ems of
           Nothing -> throw $ "Incomplete pattern match: " ++ show (Case ms mot cs)
           Just b  -> eval b