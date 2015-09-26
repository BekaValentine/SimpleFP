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

conSigLength :: (String -> a) -> ConSig a -> Int
conSigLength _ (ConSigNil _) = 0
conSigLength f (ConSigCons _ (Scope xs b))
  = 1 + conSigLength f (b (map f xs))

type Signature a = [(String,ConSig a)]