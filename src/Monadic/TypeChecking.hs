{-# LANGUAGE RecursiveDo #-}

module Monadic.TypeChecking where

import Control.Monad (guard)
import Control.Monad.Trans.Reader
import Data.List (intercalate,nub)

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
      "Constructors:\n" ++
        unlines [ "  " ++ c ++ "(" ++
                  intercalate "," (map show args) ++
                  ") : " ++ show ret
                | (c,ConSig args ret) <- consigs
                ]




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





-- Type Checking Monad

type TypeChecker a = ReaderT (Signature,Context) Maybe a

runTypeChecker :: TypeChecker a -> Signature -> Context -> Maybe a
runTypeChecker = curry.runReaderT

failure :: TypeChecker a
failure = ReaderT $ \_ -> Nothing

signature :: TypeChecker Signature
signature = do (sig,_) <- ask
               return sig

context :: TypeChecker Context
context = do (_,ctx) <- ask
             return ctx

extend :: Context -> TypeChecker a -> TypeChecker a
extend ectx = local (\(sig,ctx) -> (sig,ectx++ctx))



tyconExists :: String -> TypeChecker ()
tyconExists n = do Signature tycons _ <- signature
                   guard $ n `elem` tycons

typeInSignature :: String -> TypeChecker ConSig
typeInSignature n = do Signature _ consigs <- signature
                       case lookup n consigs of
                         Nothing -> failure
                         Just t  -> return t


typeInContext :: String -> TypeChecker Type
typeInContext x = do ctx <- context
                     go ctx
  where
    go [] = failure
    go (HasType y t  : _) | x == y = return t
    go (HasDef y _ t : _) | x == y = return t
    go (_:ctx) = go ctx



-- Type well-formedness

isType :: Type -> TypeChecker ()
isType (TyCon tc) = tyconExists tc
isType (Fun a b)  = isType a >> isType b



-- Type Inference

infer :: Term -> TypeChecker Type
infer (Var x)     = typeInContext x
infer (Ann m t)   = check m t >> return t
infer (Lam x b)   = failure
infer (App f a)   = do Fun arg ret <- infer f
                       arg' <- infer a
                       guard (arg == arg')
                       return ret
infer (Con c as)  = do ConSig args ret <- typeInSignature c
                       guard $ length as == length args
                       sequence_ (zipWith check as args)
                       return ret
infer (Case m cs) = do t <- infer m
                       t' <- inferClauses t cs
                       return t'


inferClause :: Type -> Clause -> TypeChecker Type
inferClause patTy (Clause p b) = do ctx' <- checkPattern p patTy
                                    ctx <- context
                                    extend ctx'
                                         $ infer b


inferClauses :: Type -> [Clause] -> TypeChecker Type
inferClauses patTy cs = do ts <- sequence $ map (inferClause patTy) cs
                           case ts of
                             t:ts | all (== t) ts
                               -> return t
                             _ -> failure



-- Type Checking

check :: Term -> Type -> TypeChecker ()
check (Var x)     t = do t' <- infer (Var x)
                         guard $ t == t'
check (Ann m t')  t = do guard $ t == t'
                         check m t'
check (Lam x b)   t = case t of
                        Fun arg ret
                          -> do ctx <- context
                                extend [HasType x arg]
                                     $ check b ret
                        _ -> failure
check (App f a)   t = do Fun arg ret <- infer f
                         guard $ ret == t
                         check a arg
check (Con c as)  t = do t' <- infer (Con c as)
                         guard $ t == t'
check (Case m cs) t = do t' <- infer m
                         checkClauses t' cs t


checkPattern :: Pattern -> Type -> TypeChecker Context
checkPattern patTy t = do ctx <- go patTy t
                          let names = map name ctx
                          guard $ length names == length (nub names)
                          return ctx
  where
    go (VarPat x)    t = return [HasType x t]
    go (ConPat c ps) t = do ConSig args ret <- typeInSignature c
                            guard $ length ps == length args
                                 && t == ret
                            rss <- sequence $ zipWith go ps args
                            return $ concat rss


checkClauses :: Type -> [Clause] -> Type -> TypeChecker ()
checkClauses patTy [] t = return ()
checkClauses patTy (Clause p b:cs) t = do ctx' <- checkPattern p patTy
                                          ctx <- context
                                          extend ctx'
                                               $ check b t
                                          checkClauses patTy cs t