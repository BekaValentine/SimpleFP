module Poly.Type where

data Type
  = TyCon String
  | Fun Type Type
  | TyVar String
  | Forall String Type
  deriving (Eq)

data TypeParenLoc = RootType | FunLeft | FunRight | ForallBody
  deriving (Eq)

instance Show Type where
  show t = aux RootType t
    where
      aux c t
        = let (cs, str) = case t of
                TyCon n    -> ([RootType,FunLeft,FunRight,ForallBody], n)
                Fun a b    -> ([RootType,FunRight,ForallBody], aux FunLeft a ++ " -> " ++ aux FunRight b)
                TyVar n    -> ([RootType,FunLeft,FunRight,ForallBody], n)
                Forall n b -> ([RootType,FunRight,ForallBody], "forall " ++ n ++ ". " ++ aux ForallBody b)
          in if c `elem` cs
             then str
             else "(" ++ str ++ ")"