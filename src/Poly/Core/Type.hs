{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Poly.Core.Type where

import Data.List (intercalate)

import Parens
import Scope



-- Types

data TyVariable
  = TyName String
  | TyGenerated String Int

instance Eq TyVariable where
  TyName x == TyName y = x == y
  TyGenerated _ i == TyGenerated _ j = i == j
  _ == _ = False

data Type
  = Meta Int
  | TyCon String [Type]
  | Fun Type Type
  | TyVar TyVariable
  | Forall (Scope Type Type)



-- Show Instance

instance Show TyVariable where
  show (TyName x)      = x
  show (TyGenerated x _) = x

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

instance ParenRec Type where
  parenRec (Meta i)
    = "?" ++ show i
  parenRec (TyCon n [])
    = n
  parenRec (TyCon n as)
    = n ++ " " ++ intercalate " " (map (parenthesize (Just TyConArg)) as)
  parenRec (Fun a b)
    = parenthesize (Just FunLeft) a
   ++ " -> "
   ++ parenthesize (Just FunRight) b
  parenRec (TyVar n)
    = show n
  parenRec (Forall sc)
    = "forall " ++ unwords (names sc) ++ ". "
   ++ parenthesize (Just ForallBody)
        (instantiate sc [ TyVar (TyName x) | x <- names sc ])

instance Show Type where
  show t = parenthesize Nothing t