module Poly.Type where

import Data.List (intercalate)

data Type
  = TyCon String [Type]
  | Fun Type Type
  | TyVar String
  | Forall String Type
  deriving (Eq)

data TypeParenLoc = RootType | TyConArg | FunLeft | FunRight | ForallBody
  deriving (Eq)

instance Show Type where
  show t = aux RootType t
    where
      aux c t
        = let (cs, str) = case t of
                TyCon n [] -> ([RootType,TyConArg,FunLeft,FunRight,ForallBody], n)
                TyCon n xs -> ([RootType,FunRight,ForallBody], n ++ " " ++ intercalate " " (map (aux TyConArg) xs))
                Fun a b    -> ([RootType,FunRight,ForallBody], aux FunLeft a ++ " -> " ++ aux FunRight b)
                TyVar n    -> ([RootType,TyConArg,FunLeft,FunRight,ForallBody], n)
                Forall n b -> ([RootType,FunRight,ForallBody], "forall " ++ n ++ ". " ++ aux ForallBody b)
          in if c `elem` cs
             then str
             else "(" ++ str ++ ")"