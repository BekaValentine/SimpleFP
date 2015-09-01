{-# OPTIONS -Wall #-}

module Dependent.Core.Evaluation where

import Control.Monad (forM)

import Dependent.Core.Substitution
import Dependent.Core.Term



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

eval :: Free -> Term -> Either String Term
eval _    (Meta i)     = return $ Meta i
eval _    (Var x)      = return $ Var x
eval free (Ann m _)    = eval free m
eval _    Type         = return Type
eval free (Fun x a b)  = do ea <- eval free a
                            let (x',b') = rename free x b
                            eb' <- eval (x':free) b'
                            return $ Fun x' ea eb'
eval free (Lam x b)    = do let (x',b') = rename free x b
                            eb' <- eval (x':free) b'
                            return $ Lam x' eb'
eval free (App f a)    = do ef <- eval free f
                            ea <- eval free a
                            case ef of
                              Lam x b
                                -> eval free (subst free ea x b)
                              _ -> return $ App ef ea
eval free (Con c as)   = do eas <- sequence (map (eval free) as)
                            return $ Con c eas
eval free (Case ms cs) = do ems@(CaseArgSequence ms') <- evalCaseArgSequence free ms
                            if any (\m -> case m of { Con _ _ -> False ; _ -> True }) ms'
                            then do
                              ecs <- forM cs $ \c ->
                                       do let (Clause ps' b', newFree) = freshenClause free c
                                          eb' <- eval (newFree ++ free) b'
                                          return $ Clause ps' eb'
                              return $ Case ems ecs
                            else case matchClauses cs ems of
                              Nothing       -> Left $ "Incomplete pattern match: " ++ show (Case ems cs)
                              Just (env, b) -> eval free (substMulti free env b)

evalCaseArgSequence :: Free -> CaseArgSequence -> Either String CaseArgSequence
evalCaseArgSequence free (CaseArgSequence ms)
  = do ems <- mapM (eval free ) ms
       return $ CaseArgSequence ems