{-# OPTIONS -Wall #-}

module Dependent.Core.ConSig where

import Scope

data ConSig a = ConSigNil a | ConSigCons a (Scope a (ConSig a))

showConSig :: Show a => (String -> a) -> ConSig a -> String
showConSig _ (ConSigNil a)
  = show a
showConSig f (ConSigCons a sc) | length (names sc) == 1
  = "(" ++ unwords (names sc) ++ " : " ++ show a ++ ") "
 ++ showConSig f (instantiate sc (map f (names sc)))
showConSig _ _
  = error "ConSigs should have exactly one scope argument."

conSigLength :: (String -> a) -> ConSig a -> Int
conSigLength _ (ConSigNil _) = 0
conSigLength f (ConSigCons _ sc)
  = 1 + conSigLength f (instantiate sc (map f (names sc)))

type Signature a = [(String,ConSig a)]