{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Simple.Core.Abstraction where

import Control.Monad.Reader
import qualified Control.Monad.State as S

import Abs
import Scope

import Simple.Core.Term
import Simple.Core.Type



-- Abstraction

abstractClause :: Clause -> Abstracted String Term Clause
abstractClause (Clause p sc)
  = Clause p <$> abstractScope sc

instance Abstract String Term Term where
  abstract (Var (Name x))
    = reader $ \e ->
        case lookup x e of
          Nothing -> Var (Name x)
          Just m  -> m
  abstract (Var (Generated x i))
    = return $ Var (Generated x i)
  abstract (Ann m ty)
    = Ann <$> abstract m <*> return ty
  abstract (Lam sc)
    = Lam <$> abstractScope sc
  abstract (App f a)
    = App <$> abstract f <*> abstract a
  abstract (Con c as)
    = Con c <$> mapM abstract as
  abstract (Case a cs)
    = Case <$> mapM abstract a <*> mapM abstractClause cs

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

lamHelper :: String -> Term -> Term
lamHelper x b = Lam (scope [x] b)

clauseHelper :: [Pattern] -> [String] -> Term -> Clause
clauseHelper ps xs b = Clause (scope2 xs cleanedXs cleanedPs) (scope (filter isVar xs) b)
  where
    cleanedXs = fst (S.runState (mapM cleanXs xs) 0)
    
    cleanXs :: String -> S.State Int String
    cleanXs "_" = do i <- S.get
                     S.put (i+1)
                     return $ "$" ++ show i
    cleanXs x = return x
    
    cleanedPs = fst (S.runState (mapM cleanPs ps) 0)
    
    cleanPs :: Pattern -> S.State Int Pattern
    cleanPs (VarPat (Name "_"))
      = do i <- S.get
           S.put (i+1)
           return $ VarPat (Name ("$" ++ show i))
    cleanPs (VarPat (Name n))
      = return $ VarPat (Name n)
    cleanPs (VarPat (Generated n i))
      = return $ VarPat (Generated n i)
    cleanPs (ConPat c ps)
      = ConPat c <$> mapM cleanPs ps