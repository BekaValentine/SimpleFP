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
scope xs m = Scope xs (abstractOver xs m)

scope2 :: Abstract String s a => [String] -> [String] -> a -> Scope s a
scope2 xs xs' m = Scope xs (abstractOver xs' m)

descope :: (String -> s) -> Scope s a -> a
descope f sc = instantiate sc (map f (names sc))

instance Functor (Scope s) where
  fmap f (Scope ns b) = Scope ns (f . b)

helperFold :: (a -> b -> b) -> [a] -> b -> b
helperFold c xs n = foldr c n xs

isVar :: String -> Bool
isVar "_" = False
isVar ('$':_) = False
isVar _ = True

removeByDummies :: [String] -> [a] -> [a]
removeByDummies ns xs = [ x | (n,x) <- zip ns xs, isVar n ]