{-# OPTIONS -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Eval where

import Control.Monad.Reader

import Env

type Evaluator e = ReaderT (Environment String e) (Either String)

environment :: Evaluator a (Environment String a)
environment = ask

class Eval e a where
  eval :: a -> Evaluator e a

throw :: String -> Evaluator e a
throw e = lift (Left e)