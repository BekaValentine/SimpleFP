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