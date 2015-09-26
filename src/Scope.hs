{-# LANGUAGE FlexibleContexts #-}

module Scope where

import Control.Monad.Reader

import Abs

data Scope s a
  = Scope { names :: [String], instantiate :: [s] -> a }

abstractScope :: Abstract i e a => Scope s a -> Abstracted i e (Scope s a)
abstractScope (Scope ns f)
  = reader $ \e ->
      Scope ns $ \vs' -> runReader (abstract (f vs')) e

scope :: Abstract String s a => [String] -> a -> Scope s a
scope xs m = Scope xs $ \as -> runReader (abstract m) (zip xs as)

instance Functor (Scope s) where
  fmap f (Scope ns b) = Scope ns (f . b)