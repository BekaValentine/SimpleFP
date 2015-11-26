{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Abs where

import Control.Monad.Reader

import Env

type Abstracted i e a = Reader (Environment i e) a

class Abstract i e a where
  abstract :: a -> Abstracted i e a

instance Abstract i e a => Abstract i e [a] where
  abstract = mapM abstract

abstractOver :: Abstract i e a => [i] -> a -> [e] -> a
abstractOver [] m _  = m
abstractOver xs m vs = runReader (abstract m) (zip xs vs)

abstractOverDummies :: Abstract String e a => [String] -> a -> [e] -> a
abstractOverDummies ns m vs = runReader (abstract m) (zipDummies ns vs)
  where
    zipDummies :: [String] -> [b] -> [(String,b)]
    zipDummies ("_":xs) (_:ys) = zipDummies xs ys
    zipDummies (x:xs)  (y:ys) = (x,y) : zipDummies xs ys
    zipDummies _ _ = []