{-# OPTIONS -Wall #-}

module OpenDefs.Core.ConSig where

import Plicity
import Scope

data ConSig a = ConSigNil a | ConSigCons Plicity a (Scope a (ConSig a))

showConSig :: Show a => (String -> a) -> ConSig a -> String
showConSig _ (ConSigNil a)
  = show a
showConSig f (ConSigCons plic a sc) | length (names sc) == 1
  = let a0' = unwords (names sc) ++ " : " ++ show a
        a' = case plic of
               Expl -> "(" ++ a0' ++ ") "
               Impl -> "{" ++ a0' ++ "} "
    in a' ++ showConSig f (instantiate sc (map f (names sc)))
showConSig _ _
  = error "ConSigs should have exactly one scope argument."

conSigLength :: (String -> a) -> ConSig a -> Int
conSigLength _ (ConSigNil _) = 0
conSigLength f (ConSigCons _ _ sc)
  = 1 + conSigLength f (instantiate sc (map f (names sc)))

type Signature a = [((String,String),ConSig a)]