{-# OPTIONS -Wall #-}

module Dependent.Core.ConSig where

import Scope

data ConSig a = ConSigNil a | ConSigCons a (Scope a (ConSig a))

showConSig :: Show a => (String -> a) -> ConSig a -> String
showConSig _ (ConSigNil a)
  = show a
showConSig f (ConSigCons a (Scope [x] b))
  = "(" ++ x ++ " : " ++ show a ++ ") " ++ showConSig f (b [f x])
showConSig _ _
  = error "ConSigs should have exactly one scope argument."

type Signature a = [(String,ConSig a)]