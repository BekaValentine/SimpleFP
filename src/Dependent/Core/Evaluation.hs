{-# OPTIONS -Wall #-}

module Dependent.Core.Evaluation where

import Control.Monad (forM)
import Data.List (foldl'  )

import Dependent.Core.Term


-- Evaluation Environments

type Env = [(String,Term)]

lookupEnv :: String -> Env -> Maybe Term
lookupEnv = lookup

removeEnv :: String -> Env -> Env
removeEnv x = filter (\(y,_) -> x /= y)

removeEnvPattern :: Env -> Pattern -> Env
removeEnvPattern env (VarPat x) = removeEnv x env
removeEnvPattern env (ConPat _ ps)
  = foldl' removeEnvPattern env ps

removeEnvPatternSequence :: Env -> PatternSequence -> Env
removeEnvPatternSequence env (PatternSequence ps)
  = foldl' removeEnvPattern env ps



-- Pattern Matching

match :: Pattern -> Term -> Maybe Env
match (VarPat x) v = Just [(x,v)]
match (ConPat c ps) (Con c' as) | c == c' && length ps == length as
  = fmap concat (sequence (zipWith match ps as))
match _ _ = Nothing

matchSequence :: PatternSequence -> CaseArgSequence -> Maybe Env
matchSequence (PatternSequence ps0) (CaseArgSequence ms0) = go ps0 ms0
  where
    go :: [Pattern] -> [Term] -> Maybe Env
    go []     []     = Just []
    go (p:ps) (m:ms) = do env <- match p m
                          envs <- go ps ms
                          return $ env ++ envs
    go _      _      = Nothing

matchClauses :: [Clause] -> CaseArgSequence -> Maybe (Env,Term)
matchClauses []               _ = Nothing
matchClauses (Clause ps b:cs) v = case matchSequence ps v of
                                    Nothing   -> matchClauses cs v
                                    Just env' -> Just (env',b)



-- Standard Eager Evaluation

eval :: Env -> Term -> Either String Term
eval env (Var x)      = case lookupEnv x env of
                          Nothing -> return $ Var x
                          Just m  -> return m
eval env (Ann m _)    = eval env m
eval _   Type         = return Type
eval env (Fun x a b)  = do ea <- eval env a
                           eb <- eval (removeEnv x env) b
                           return $ Fun x ea eb
eval env (Lam x b)    = do eb <- eval (removeEnv x env) b
                           return $ Lam x eb
eval env (App f a)    = do ef <- eval env f
                           ea <- eval env a
                           case (ef, ea) of
                             (Lam x b, a') -> eval ((x,a'):env) b
                             _ -> return $ App ef ea
eval env (Con c as)   = do eas <- sequence (map (eval env) as)
                           return $ Con c eas
eval env (Case ms cs) = do ems@(CaseArgSequence ms') <- evalCaseArgSequence env ms
                           if any (\m -> case m of { Con _ _ -> False ; _ -> True }) ms'
                           then do
                             ecs <- forM cs $ \(Clause ps b) ->
                                      do eb <- eval (removeEnvPatternSequence env ps) b
                                         return $ Clause ps eb
                             return $ Case ems ecs
                           else case matchClauses cs ems of
                             Nothing        -> Left $ "Incomplete pattern match: " ++ show (Case ems cs)
                             Just (env', b) -> eval (env'++env) b

evalCaseArgSequence :: Env -> CaseArgSequence -> Either String CaseArgSequence
evalCaseArgSequence env (CaseArgSequence ms)
  = do ems <- mapM (eval env) ms
       return $ CaseArgSequence ems