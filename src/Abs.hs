{-# OPTIONS -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Abs where

import Control.Monad.Reader

import Env

type Abstracted i e a = Reader (Environment i e) a

class Abstract i e a where
  abstract :: a -> Abstracted i e a