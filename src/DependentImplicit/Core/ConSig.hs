{-# OPTIONS -Wall #-}

module DependentImplicit.Core.ConSig where

import Plicity
import Scope

data ConSig a = ConSigNil a | ConSigCons Plicity a (Scope a (ConSig a))

showConSig :: Show a => (String -> a) -> ConSig a -> String
showConSig _ (ConSigNil a)
  = show a
showConSig f (ConSigCons plic a (Scope [x] b))
  = let a0' = x ++ " : " ++ show a
        a' = case plic of
               Expl -> "(" ++ a0' ++ ") "
               Impl -> "{" ++ a0' ++ "} "
    in a' ++ showConSig f (b [f x])
showConSig _ _
  = error "ConSigs should have exactly one scope argument."

conSigLength :: (String -> a) -> ConSig a -> Int
conSigLength _ (ConSigNil _) = 0
conSigLength f (ConSigCons _ _ (Scope xs b))
  = 1 + conSigLength f (b (map f xs))

type Signature a = [(String,ConSig a)]