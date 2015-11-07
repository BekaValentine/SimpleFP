{-# OPTIONS -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Abs where

import Control.Monad.Reader

import Env

type Abstracted i e a = Reader (Environment i e) a

class Abstract i e a where
  abstract :: a -> Abstracted i e a

abstractOver :: Abstract i e a => [i] -> a -> [e] -> a
abstractOver [] m _  = m
abstractOver xs m vs = runReader (abstract m) (zip xs vs)

abstractOverDummies :: Abstract i e a => [Maybe i] -> a -> [e] -> a
abstractOverDummies xs m vs = runReader (abstract m) (zipDummies xs vs)
  where
    zipDummies :: [Maybe a] -> [b] -> [(a,b)]
    zipDummies (Nothing:xs) (_:ys) = zipDummies xs ys
    zipDummies (Just x:xs)  (y:ys) = (x,y) : zipDummies xs ys
    zipDummies _ _ = []