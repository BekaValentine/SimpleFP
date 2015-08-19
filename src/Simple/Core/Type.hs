module Simple.Core.Type where

data Type
  = TyCon String
  | Fun Type Type
  deriving (Eq)

data TypeParenLoc = RootType | FunLeft | FunRight
  deriving (Eq)

instance Show Type where
  show t = aux RootType t
    where
      aux c t
        = let (cs, str) = case t of
                TyCon n -> ([RootType,FunLeft,FunRight], n)
                Fun a b -> ([RootType,FunRight], aux FunLeft a ++ " -> " ++ aux FunRight b)
          in if c `elem` cs
             then str
             else "(" ++ str ++ ")"