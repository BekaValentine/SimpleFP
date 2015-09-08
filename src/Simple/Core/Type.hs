{-# OPTIONS -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Simple.Core.Type where

import Control.Monad.Identity

import Parens



-- Types

data Type
  = TyCon String
  | Fun Type Type
  deriving (Eq)



-- Show Instance

data TypeParenLoc = FunLeft | FunRight
  deriving (Eq)

instance ParenLoc Type where
  type Loc Type = TypeParenLoc
  parenLoc (TyCon _) = [FunLeft,FunRight]
  parenLoc (Fun _ _) = [FunRight]

instance ParenRec Identity Type where
  parenRec (TyCon c) = Identity c
  parenRec (Fun a b) = let Identity sa = parenthesize (Just FunLeft) a
                           Identity sb = parenthesize (Just FunRight) b
                       in Identity (sa ++ " -> " ++ sb)

instance Show Type where
  show t = runIdentity (parenthesize Nothing t)
    {-
    aux RootType t
    where
      aux c t
        = let (cs, str) = case t of
                TyCon n -> ([RootType,FunLeft,FunRight], n)
                Fun a b -> ([RootType,FunRight], aux FunLeft a ++ " -> " ++ aux FunRight b)
          in if c `elem` cs
             then str
             else "(" ++ str ++ ")"
             -}