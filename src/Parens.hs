{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Parens where

class ParenLoc a where
  type Loc a
  parenLoc :: a -> [Loc a]

class ParenRec a where
  parenRec :: a -> String

parenthesize :: (ParenLoc a, Eq (Loc a), ParenRec a) => Maybe (Loc a) -> a -> String
parenthesize l x
  = let rec = parenRec x
    in case l of
         Nothing
           -> rec
         Just loc | loc `elem` parenLoc x
           -> rec
         _ -> "(" ++ rec ++ ")"