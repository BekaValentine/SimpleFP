{-# LANGUAGE RecursiveDo #-}

module Algebraic.TypeChecking where

import Control.Applicative ((<$>),(<*>))
import Control.Monad (guard)
import Data.List (intercalate,nub)
import Data.Maybe (isJust)

import Core.Term
import Core.Type
import Core.Evaluation



-- Signatures

data ConSig = ConSig [Type] Type

instance Show ConSig where
  show (ConSig as r) = "(" ++ intercalate "," (map show as) ++ ")" ++ show r

data Signature = Signature [String] [(String,ConSig)]

instance Show Signature where
  show (Signature tycons consigs)
    = "Types: " ++ unwords tycons ++ "\n" ++
      "Constructors:\n" ++ unlines [ "  " ++ c ++ "(" ++ intercalate "," (map show args) ++ ") : " ++ show ret  | (c,ConSig args ret) <- consigs ]


-- Contexts

data Declaration
  = HasType String Type
  | HasDef String Term Type

instance Show Declaration where
  show (HasType x t)  = x ++ " : " ++ show t
  show (HasDef x v t) = x ++ " = " ++ show v ++ " : " ++ show t

name :: Declaration -> String
name (HasType n _)  = n
name (HasDef n _ _) = n

type Context = [Declaration]

contextToEnv :: Context -> Either String Env
contextToEnv [] = return []
contextToEnv (HasDef x m _:ctx)
  = do env <- contextToEnv ctx
       rec v <- eval ((x,v):env) m
       return $ (x,v):env
contextToEnv (_:ctx) = contextToEnv ctx




type TypeChecker a = Signature -> Context -> Maybe a

typeInContext :: String -> TypeChecker Type
typeInContext _ _ [] = Nothing
typeInContext x _ (HasType y t  : _) | x == y = Just t
typeInContext x _ (HasDef y _ t : _) | x == y = Just t
typeInContext x sig (_:ctx) = typeInContext x sig ctx

tyconExists :: String -> TypeChecker () --Signature -> Bool
tyconExists n (Signature tycons _) _
  = if n `elem` tycons
    then Just ()
    else Nothing

typeInSignature :: String -> TypeChecker ConSig --Signature -> Maybe ConSig
typeInSignature n (Signature _ consigs) _ = lookup n consigs



-- Type well-formedness

isType :: Type -> TypeChecker Type
isType (TyCon tc) sig ctx = tyconExists tc sig ctx >> return (TyCon tc)
isType (Fun a b)  sig ctx = Fun <$> isType a sig ctx <*> isType b sig ctx



-- Combinators

failure :: TypeChecker a
failure = \sig ctx -> Nothing

ivar :: String -> TypeChecker Type
ivar x = typeInContext x

iann :: (Type -> TypeChecker ()) -> TypeChecker Type -> TypeChecker Type
iann m t = \sig ctx ->
             do t' <- t sig ctx
                m t' sig ctx
                return t'

iapp :: TypeChecker Type -> TypeChecker Type -> TypeChecker Type
iapp f a = \sig ctx ->
             do Fun arg ret <- f sig ctx
                arg' <- a sig ctx
                guard (arg == arg')
                return ret

icon :: String -> [Type -> TypeChecker ()] -> TypeChecker Type
icon c as = \sig ctx ->
               do ConSig args ret <- typeInSignature c sig ctx
                  guard $ length as == length args
                  sequence_ (zipWith (\t a -> t a sig ctx) as args)
                  return ret

icase :: TypeChecker Type -> (Type -> TypeChecker Type) ->TypeChecker Type
icase m cs = \sig ctx ->
               do t <- m sig ctx
                  t' <- cs t sig ctx
                  return t'

iclause :: TypeChecker Context -> TypeChecker Type -> TypeChecker Type
iclause p b = \sig ctx ->
                do ctx' <- p sig ctx
                   b sig (ctx'++ctx)

iclauses :: [Type -> TypeChecker Type] -> Type -> TypeChecker Type
iclauses cs t = \sig ctx ->
                  do ts <- sequence [ c t sig ctx | c <- cs ]
                     case ts of
                       t:ts' | all (==t) ts'
                         -> return t
                       _ -> Nothing

cvar :: String -> Type -> TypeChecker ()
cvar x t = \sig ctx ->
             do t' <- ivar x sig ctx
                guard (t == t')

cann :: (Type -> TypeChecker ()) -> Type -> Type -> TypeChecker ()
cann m t' t = \sig ctx ->
                do guard (t' == t)
                   m t sig ctx

clam :: String -> (Type -> TypeChecker ()) -> Type -> TypeChecker ()
clam x b (Fun arg ret) = \sig ctx ->
                           b ret sig (HasType x arg : ctx)
clam x b _ = failure



-- Type Inference

infer :: Term -> TypeChecker Type
infer (Var x)     = ivar x
infer (Ann m t)   = iann (check m) (isType t)
infer (Lam x b)   = failure
infer (App f a)   = iapp (infer f) (infer a)
infer (Con c as)  = icon c (map check as)
infer (Case m cs) = icase (infer m) (inferClauses cs)

inferClause :: Clause -> Type -> TypeChecker Type
inferClause (Clause p b) t = iclause (checkPattern p t) (infer b)

inferClauses :: [Clause] -> Type -> TypeChecker Type
inferClauses cs t = iclauses (map inferClause cs) t



-- Type Checking

check :: Term -> Type -> TypeChecker ()
check (Var x)    t  sig ctx = cvar x t sig ctx
check (Ann m t') t  sig ctx = cann (check m) t' t sig ctx
check (Lam x b)  t  sig ctx = clam x (check b) t sig ctx
check (App f a)  t  sig ctx = case infer f sig ctx of
                                Just (Fun arg ret)
                                  -> if ret == t
                                     then check a arg sig ctx
                                     else Nothing
                                _ -> Nothing
check (Con c as) t  sig ctx = case infer (Con c as) sig ctx of
                                Just t' | t == t'
                                  -> return ()
                                _ -> Nothing
check (Case m cs) t sig ctx = case infer m sig ctx of
                                Nothing -> Nothing
                                Just t' -> checkClauses t' cs t sig ctx


checkPattern :: Pattern -> Type -> TypeChecker Context
checkPattern p t sig ctx = do ctx' <- go p t
                              let names = map name ctx'
                              guard $ length names == length (nub names)
                              return ctx'
  where
    go (VarPat x)    t = Just [HasType x t]
    go (ConPat c ps) t = do ConSig args ret <- typeInSignature c sig ctx
                            guard $ length ps == length args
                                 && t == ret
                            fmap concat (sequence (zipWith go ps args))


checkClauses :: Type -> [Clause] -> Type -> TypeChecker ()
checkClauses patTy [] t sig ctx = return ()
checkClauses patTy (Clause p b:cs) t sig ctx
  = case checkPattern p patTy sig ctx of
      Nothing   -> Nothing
      Just ctx' -> check b t sig (ctx'++ctx) >> checkClauses patTy cs t sig ctx