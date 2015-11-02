{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Record.Core.Evaluation where

import Control.Monad.Except

import Env
import Eval
import Plicity
import Scope
import Record.Core.Term




--
-- NOTE
--
-- Plicity mismatches should never occur in evaluable code, so they throw
-- actual Haskell errors, not internal language errors.
--


-- Pattern Matching

matchPattern :: Pattern -> Term -> Maybe [Term]
matchPattern (VarPat _) v = Just [v]
matchPattern (ConPat c ps) (Con c' as) | c == c'
  = matchPatternSeq ps as
matchPattern (AssertionPat _) _ = Just []
matchPattern _ _ = Nothing

matchPatternSeq :: PatternSeq -> [(Plicity,Term)] -> Maybe [Term]
matchPatternSeq PatternSeqNil []
  = Just []
matchPatternSeq (PatternSeqCons plic p sc) ((plic',m):ms)
  | plic == plic'
    = do vs <- matchPattern p m
         vs' <- matchPatternSeq (descope (Var . Name) sc) ms
         return $ vs ++ vs'
  | otherwise
    = error "Mismatching plicity in pattern match."
matchPatternSeq _ _
  = Nothing

matchClauses :: [Clause] -> [(Plicity,Term)] -> Maybe Term
matchClauses [] _ = Nothing
matchClauses (Clause ps sc:cs) ms
  = case matchPatternSeq ps ms of
      Nothing -> matchClauses cs ms
      Just vs -> Just (instantiate sc vs)



-- Standard Eager Evaluation

instance Eval (Environment (String,String) Term) Term where
  eval (Meta i)
    = return $ Meta i
  eval (Var x)
    = return $ Var x
  eval (DottedVar mdl var)
    = do env <- environment
         case lookup (mdl,var) env of
           Nothing -> throwError $ "Unknown constant/defined term: " ++ show (DottedVar mdl var)
           Just m  -> eval m
  eval (Ann m _)
    = eval m
  eval Type
    = return Type
  eval (Fun plic a sc)
    = return $ Fun plic a sc
  eval (Lam plic sc)
    = return $ Lam plic sc
  eval (App plic f a)
    = do ef <- eval f
         ea <- eval a
         case ef of
           Lam plic' sc
             | plic == plic' -> eval (instantiate sc [ea])
             | otherwise     -> error "Mismatching plicity in function application."
           _ -> return $ App plic ef ea
  eval (Con c as)
    = do eas <- forM as $ \(plic,a) ->
                  do a' <- eval a
                     return (plic,a')
         return $ Con c eas
  eval (Case ms mot cs)
    = do ems <- mapM eval ms
         case matchClauses cs [ (Expl,em) | em <- ems ] of
           Nothing -> return (Case ms mot cs)
           Just b  -> eval b
  eval (OpenIn _ m)
    = eval m
  eval (RecordType tele)
    = return $ RecordType tele
  eval (RecordCon fields)
    = RecordCon <$> sequenceA [ (,) x <$> eval m | (x,m) <- fields ]
  eval (RecordDot m x)
    = do em <- eval m
         case em of
           RecordCon fields -> case lookup x fields of
             Nothing -> throwError $ "Unknown field '" ++ x ++ "' in record " ++ show (RecordCon fields)
             Just m' -> return m'
           m' -> return $ RecordDot m' x