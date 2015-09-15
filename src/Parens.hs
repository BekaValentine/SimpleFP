{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Parens where

class ParenLoc a where
  type Loc a
  parenLoc :: a -> [Loc a]

class ParenBound a where
  parenBound :: a -> [String] -> String

parenthesizeBound :: (ParenLoc a, Eq (Loc a), ParenBound a) => Maybe (Loc a) -> a -> [String] -> String
parenthesizeBound l x ns
  = let rec = parenBound x ns
    in case l of
         Just loc | loc `elem` parenLoc x
           -> rec
         _ -> "(" ++ rec ++ ")"

class ParenRec a where
  parenRec :: a -> String

parenthesize :: (ParenLoc a, Eq (Loc a), ParenRec a) => Maybe (Loc a) -> a -> String
parenthesize l x
  = let rec = parenRec x
    in case l of
         Just loc | loc `elem` parenLoc x
           -> rec
         _ -> "(" ++ rec ++ ")"