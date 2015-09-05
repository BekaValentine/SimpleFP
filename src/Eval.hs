{-# OPTIONS -Wall #-}

module Eval where

import Control.Monad.Reader

import Env

type Evaluator a = ReaderT (Environment a) (Either String)

environment :: Evaluator a (Environment a)
environment = ask

class Eval a where
  eval :: a -> Evaluator a a

throw :: String -> Evaluator a b
throw e = lift (Left e)