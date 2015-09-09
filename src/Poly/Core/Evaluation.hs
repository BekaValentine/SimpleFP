module Poly.Core.Evaluation where

import Control.Monad (zipWithM)
import Data.List (intercalate)

import Eval
import Scope
import Poly.Core.Term


-- Pattern Matching

match :: Pattern -> Term -> Maybe [Term]
match VarPat v = Just [v]
match (ConPat c ps) (Con c' as)
  | c == c' && length ps == length as
  = fmap concat (zipWithM match ps as)
match _ _ = Nothing

matchClauses :: [Clause] -> Term -> Maybe Term
matchClauses [] _
  = Nothing
matchClauses (Clause p sc:cs) v
  = case match p v of
      Nothing -> matchClauses cs v
      Just xs -> Just (instantiate sc xs)



-- Standard Eager Evaluation

instance Eval Term where
  eval (Var (Name x))
    = do env <- environment
         case lookup x env of
           Nothing -> throw ("Unbound variable: " ++ x ++ "\nEnvironment: " ++ show env)
           Just m  -> return m
  eval (Var (Generated i))
    = return $ Var (Generated i)
  eval (Ann m _)
    = eval m
  eval (Lam sc)
    = return $ Lam sc
  eval (App f a)
    = do ef <- eval f
         ea <- eval a
         case (ef, ea) of
           (Lam sc, a') -> eval (instantiate sc [ea])
           (_,_)        -> return $ App ef ea
  eval (Con c as)
    = do eas <- mapM eval as
         return $ Con c eas
  eval (Case m cs)
    = do em <- eval m
         case matchClauses cs em of
           Nothing -> throw $ "Incomplete pattern match: " ++ show (Case m cs)
           Just b  -> eval b