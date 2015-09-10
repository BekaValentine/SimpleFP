module Scope where

import Control.Monad.Reader

import Abs

data Scope s a
  = Scope { instantiate :: [s] -> a }

abstractScope :: Abstract i e a => Scope s a -> Abstracted i e (Scope s a)
abstractScope (Scope f)
  = reader $ \e ->
      Scope $ \vs' -> runReader (abstract (f vs')) e