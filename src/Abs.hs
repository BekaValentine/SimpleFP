{-# OPTIONS -Wall #-}

module Abs where

import Control.Monad.Reader

import Env

type Abstracted a = Reader (Environment a)

class Abstract a where
  abstract :: a -> Abstracted a a