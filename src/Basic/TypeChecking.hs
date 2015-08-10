{-# LANGUAGE RecursiveDo #-}

module Basic.TypeChecking where

import Control.Monad (guard)
import Data.List (intercalate,nub)

import Core.Term
import Core.Type
import Core.Evaluation




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

typeInContext :: String -> Context -> Maybe Type
typeInContext _ [] = Nothing
typeInContext x (HasType y t  : _) | x == y = Just t
typeInContext x (HasDef y _ t : _) | x == y = Just t
typeInContext x (_:ctx) = typeInContext x ctx

contextToEnv :: Context -> Either String Env
contextToEnv [] = return []
contextToEnv (HasDef x m _:ctx)
  = do env <- contextToEnv ctx
       rec v <- eval ((x,v):env) m
       return $ (x,v):env
contextToEnv (_:ctx) = contextToEnv ctx



-- Signatures

data ConSig = ConSig [Type] Type

instance Show ConSig where
  show (ConSig as r) = "(" ++ intercalate "," (map show as) ++ ")" ++ show r

data Signature = Signature [String] [(String,ConSig)]

instance Show Signature where
  show (Signature tycons consigs)
    = "Types: " ++ unwords tycons ++ "\n" ++
      "Constructors:\n" ++ unlines [ "  " ++ c ++ "(" ++ intercalate "," (map show args) ++ ") : " ++ show ret  | (c,ConSig args ret) <- consigs ]

tyconExists :: String -> Signature -> Bool
tyconExists n (Signature tycons _) = n `elem` tycons

typeInSignature :: String -> Signature -> Maybe ConSig
typeInSignature n (Signature _ consigs) = lookup n consigs



-- Type well-formedness

isType :: Signature -> Type -> Bool
isType sig (TyCon tc) = tyconExists tc sig
isType sig (Fun a b)  = isType sig a && isType sig b



-- Type Inference

infer :: Signature -> Context -> Term -> Maybe Type
infer sig ctx (Var x)     = typeInContext x ctx
infer sig ctx (Ann m t)   = if check sig ctx m t
                            then return t
                            else Nothing
infer sig ctx (Lam x b)   = Nothing
infer sig ctx (App f a)   = do Fun arg ret <- infer sig ctx f
                               guard $ check sig ctx a arg
                               return ret
infer sig ctx (Con c as)  = do ConSig args ret <- typeInSignature c sig
                               guard $ length as == length args
                                    && and (zipWith (check sig ctx) as args)
                               return ret
infer sig ctx (Case m cs) = do t <- infer sig ctx m
                               t' <- inferClauses sig ctx t cs
                               return t'

inferClause :: Signature -> Context -> Type -> Clause -> Maybe Type
inferClause sig ctx patTy (Clause p b) = case checkPattern sig p patTy of
                                           Nothing -> Nothing
                                           Just ctx' -> infer sig (ctx'++ctx) b

inferClauses :: Signature -> Context -> Type -> [Clause] -> Maybe Type
inferClauses sig ctx patTy cs = let mts = sequence $ do
                                            Clause p b <- cs
                                            case checkPattern sig p patTy of
                                              Nothing   -> return Nothing
                                              Just ctx' -> return (infer sig (ctx'++ctx) b)
                                in case mts of
                                     Just (t:ts) | all (== t) ts
                                       -> Just t
                                     _ -> Nothing



-- Type Checking

check :: Signature -> Context -> Term -> Type -> Bool
check sig ctx (Var x)     t = case infer sig ctx (Var x) of
                                Just t' -> t == t'
                                Nothing -> False
check sig ctx (Ann m t')  t = t == t' && check sig ctx m t'
check sig ctx (Lam x b)   t = case t of
                                Fun arg ret
                                  -> check sig (HasType x arg : ctx) b ret
                                _ -> False
check sig ctx (App f a)   t = case infer sig ctx f of
                                Just (Fun arg ret)
                                  -> ret == t && check sig ctx a arg
                                _ -> False
check sig ctx (Con c as)  t = case infer sig ctx (Con c as) of
                                Nothing -> False
                                Just t' -> t == t'
check sig ctx (Case m cs) t = case infer sig ctx m of
                                Nothing -> False
                                Just t' -> checkClauses sig ctx t' cs t


checkPattern :: Signature -> Pattern -> Type -> Maybe Context
checkPattern sig p t = do ctx <- go p t
                          let names = map name ctx
                          guard $ length names == length (nub names)
                          return ctx
  where
    go (VarPat x)    t = Just [HasType x t]
    go (ConPat c ps) t = do ConSig args ret <- typeInSignature c sig
                            guard $ length ps == length args
                                 && t == ret
                            fmap concat (sequence (zipWith go ps args))


checkClauses :: Signature -> Context -> Type -> [Clause] -> Type -> Bool
checkClauses sig ctx patTy [] t = True
checkClauses sig ctx patTy (Clause p b:cs) t
  = case checkPattern sig p patTy of
      Nothing   -> False
      Just ctx' -> check sig (ctx'++ctx) b t && checkClauses sig ctx patTy cs t