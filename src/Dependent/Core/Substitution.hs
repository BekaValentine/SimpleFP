{-# OPTIONS -Wall #-}

module Dependent.Core.Substitution where

import Data.List (foldl')

import Dependent.Core.Term

type Free = [String]


freshen :: Free -> String -> String
freshen free x
  | x `elem` free = freshen free (x ++ "'")
  | otherwise     = x


subst :: Free -> Term -> String -> Term -> Term
subst _ _ _ (Meta i) = Meta i
subst _ m x (Var y)
  | x == y    = m
  | otherwise = Var y
subst free m x (Ann n t)    = Ann (subst free m x n) (subst free m x t)
subst _    _ _ Type         = Type
subst free m x (Fun y a b)  = let y' = freshen free y
                                  a' = subst free m x a
                                  b' = subst (y':free) m x (subst free (Var y') y b)
                              in Fun y' a' b'
subst free m x (Lam y b)    = let y' = freshen free y
                                  b' = subst (y':free) m x (subst free (Var y') y b)
                              in Lam y' b'
subst free m x (App f a)    = App (subst free m x f) (subst free m x a)
subst free m x (Con c as)   = Con c (map (subst free m x) as)
subst free m x (Case sq cs) = let sq' = substCaseArgSequence free m x sq
                                  cs' = map (substClause free m x) cs
                              in Case sq' cs'


substCaseArgSequence :: Free -> Term -> String -> CaseArgSequence -> CaseArgSequence
substCaseArgSequence free m x (CaseArgSequence ns) = CaseArgSequence (map (subst free m x) ns)


type Env = [(String,Term)]

substMulti :: Free -> Env -> Term -> Term
substMulti _    []          n = n
substMulti free ((x,m):env) n = substMulti free env (subst free m x n)


freshenPattern :: Free -> Pattern -> (Pattern,[(String,String)])
freshenPattern free (VarPat x)
  = let x' = freshen free x
    in (VarPat x', [(x,x')])
freshenPattern free (ConPat c as)
  = let (as',subs) = freshenPatterns free as
    in (ConPat c as', subs)

freshenPatterns :: Free -> [Pattern] -> ([Pattern],[(String,String)])
freshenPatterns _ [] = ([], [])
freshenPatterns free (p:ps)
  = let (p',subs) = freshenPattern free p
        (ps',subs') = freshenPatterns (map snd subs ++ free) ps
    in (p':ps', subs ++ subs')

freshenPatternSequence :: Free -> PatternSequence -> (PatternSequence,[(String,String)])
freshenPatternSequence free (PatternSequence ps)
  = let (ps',subs) = freshenPatterns free ps
    in (PatternSequence ps', subs)

freshenClause :: Free -> Clause -> (Clause,[String])
freshenClause free (Clause ps b)
  = let (ps',subs) = freshenPatternSequence free ps
        newFree = map snd subs
        b' = substMulti (newFree ++ free) [ (x, Var x') | (x,x') <- subs ] b
    in (Clause ps' b', newFree)


substClause :: Free -> Term -> String -> Clause -> Clause
substClause free m x (Clause ps b)
  = let (ps', subs) = freshenPatternSequence free ps
        fresh_b = foldl' (\n (y,y') -> subst free (Var y') y n) b subs
        b' = subst (map snd subs ++ free) m x fresh_b
    in Clause ps' b'


rename :: Free -> String -> Term -> (String,Term)
rename free x m = let x' = freshen free x
                  in (x,subst free (Var x') x m)


substMeta :: Term -> Int -> Term -> Term
substMeta _ _ (Var x) = Var x
substMeta m i (Meta j)
  | i == j    = m
  | otherwise = Meta j
substMeta m i (Ann n t)    = Ann (substMeta m i n) (substMeta m i t)
substMeta _ _ Type         = Type
substMeta m i (Fun x a b)  = Fun x (substMeta m i a) (substMeta m i b)
substMeta m i (Lam x b)    = Lam x (substMeta m i b)
substMeta m i (App f a)    = App (substMeta m i f) (substMeta m i a)
substMeta m i (Con c as)   = Con c (map (substMeta m i) as)
substMeta m i (Case as cs) = Case (substMetaCaseArgSequence m i as)
                                  (map (substMetaClause m i) cs)

substMetaCaseArgSequence :: Term -> Int -> CaseArgSequence -> CaseArgSequence
substMetaCaseArgSequence m i (CaseArgSequence as)
  = CaseArgSequence (map (substMeta m i) as)

substMetaClause :: Term -> Int -> Clause -> Clause
substMetaClause m i (Clause ps b) = Clause ps (substMeta m i b)