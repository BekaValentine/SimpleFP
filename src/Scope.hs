module Scope where

data Scope a
  = Scope { instantiate :: [a] -> a }