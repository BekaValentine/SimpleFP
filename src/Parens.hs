{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Parens where

class ParenLoc a where
  type Loc a
  parenLoc :: a -> [Loc a]

class ParenBound m a where
  parenBound :: a -> m (String,[Int])

parenthesizeBound :: (ParenLoc a, Eq (Loc a), ParenBound m a, Functor m) => Maybe (Loc a) -> a -> m (String,[Int])
parenthesizeBound l x
  = let rec = parenBound x
    in case l of
         Just loc | loc `elem` parenLoc x
           -> rec
         _ -> fmap (\(s,ns) -> ("(" ++ s ++ ")", ns)) rec

class ParenRec m a where
  parenRec :: a -> m String

parenthesize :: (ParenLoc a, Eq (Loc a), ParenRec m a, Functor m) => Maybe (Loc a) -> a -> m String
parenthesize l x
  = let rec = parenRec x
    in case l of
         Just loc | loc `elem` parenLoc x
           -> rec
         _ -> fmap (\s -> "(" ++ s ++ ")") rec