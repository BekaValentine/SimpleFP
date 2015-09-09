{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Poly.Core.Type where

import Control.Monad.State
import Data.List (intercalate)

import Parens
import Scope



-- Types

data TyVariable
  = TyName String
  | TyGenerated Int
  deriving (Eq)

data Type
  = Meta Int
  | TyCon String [Type]
  | Fun Type Type
  | TyVar TyVariable
  | Forall (Scope Type Type)



-- Show Instance

instance Show TyVariable where
  show (TyName x)      = x
  show (TyGenerated i) = "_" ++ show i

next :: State Int Int
next = do i <- get
          put (i+1)
          return i

data TypeParenLoc = TyConArg | FunLeft | FunRight | ForallBody
  deriving (Eq)

instance ParenLoc Type where
  type Loc Type = TypeParenLoc
  parenLoc (Meta _)     = [TyConArg,FunLeft,FunRight,ForallBody]
  parenLoc (TyCon _ []) = [TyConArg,FunLeft,FunRight,ForallBody]
  parenLoc (TyCon _ _)  = [FunRight,ForallBody]
  parenLoc (Fun _ _)    = [FunRight,ForallBody]
  parenLoc (TyVar _)    = [TyConArg,FunLeft,FunRight,ForallBody]
  parenLoc (Forall _)   = [FunRight,ForallBody]

instance ParenRec (State Int) Type where
  parenRec (Meta i)
    = return $ "?" ++ show i
  parenRec (TyCon n [])
    = return n
  parenRec (TyCon n as)
    = do as' <- mapM (parenthesize (Just TyConArg)) as
         return $ n ++ " " ++ intercalate " " as'
  parenRec (Fun a b)
    = do a' <- parenthesize (Just FunLeft) a
         b' <- parenthesize (Just FunRight) b
         return $ a' ++ " -> " ++ b'
  parenRec (TyVar n)
    = return $ show n
  parenRec (Forall sc)
    = do i <- next
         b' <- parenthesize (Just ForallBody)
                 (instantiate sc [TyVar (TyGenerated i)])
         return $ "forall " ++ show i ++ ". " ++ b'

instance Show Type where
  show t = fst (runState (parenRec t) (0 :: Int))