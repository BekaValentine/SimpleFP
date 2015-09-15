{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Parens where

import Control.Monad.State

class ParenLoc a where
  type Loc a
  parenLoc :: a -> [Loc a]

class ParenBound a where
  parenBound :: a -> State [String] String

parenthesizeBound :: (ParenLoc a, Eq (Loc a), ParenBound a) => Maybe (Loc a) -> a -> State [String] String
parenthesizeBound l x
  = do rec <- parenBound x
       case l of
         Just loc | loc `elem` parenLoc x
           -> return rec
         _ -> return $ "(" ++ rec ++ ")"

nextName :: State [String] String
nextName = do x:xs <- get
              put xs
              return x

parenthesizeBoundAtNames :: (ParenLoc a, Eq (Loc a), ParenBound a) => Maybe (Loc a) -> a -> [String] -> String
parenthesizeBoundAtNames l x ns = fst (runState (parenthesizeBound l x) ns)

class ParenRec a where
  parenRec :: a -> String

parenthesize :: (ParenLoc a, Eq (Loc a), ParenRec a) => Maybe (Loc a) -> a -> String
parenthesize l x
  = let rec = parenRec x
    in case l of
         Just loc | loc `elem` parenLoc x
           -> rec
         _ -> "(" ++ rec ++ ")"