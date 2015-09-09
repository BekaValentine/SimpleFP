module Scope where

data Scope s a
  = Scope { instantiate :: [s] -> a }