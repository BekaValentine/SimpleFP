{-# LANGUAGE RecursiveDo #-}

module Constraint.TypeChecking where

import System.IO.Unsafe

import Control.Monad (guard)
import Control.Monad.Trans.State
import Data.List (intercalate,nub)
import qualified Data.Map as M
import Data.Maybe (fromMaybe,fromJust)

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

lookupSignature :: String -> Signature -> Maybe ConSig
lookupSignature c (Signature _ consigs) = lookup c consigs


-- Pattern Types
data PatternType
  = PTyCon String
  | PFun PatternType PatternType
  | PMeta Int
  deriving (Eq,Show)

typeToPatternType :: Type -> PatternType
typeToPatternType (TyCon tycon) = PTyCon tycon
typeToPatternType (Fun a b)     = PFun (typeToPatternType a) (typeToPatternType b)

patternTypeToType :: PatternType -> Type
patternTypeToType (PTyCon tycon) = TyCon tycon
patternTypeToType (PFun a b)     = Fun (patternTypeToType a) (patternTypeToType b)
patternTypeToType (PMeta _)      = error "Cannot convert metavars to types."



-- Contexts

data Declaration
  = HasType String Type
  | HasDef String Term Type

instance Show Declaration where
  show (HasType x t)  = x ++ " : " ++ show t
  show (HasDef x v t) = x ++ " = " ++ show v ++ " : " ++ show t

type Context = [Declaration]

contextToEnv :: Context -> Either String Env
contextToEnv [] = return []
contextToEnv (HasDef x m _:ctx)
  = do env <- contextToEnv ctx
       rec v <- eval ((x,v):env) m
       return $ (x,v):env
contextToEnv (_:ctx) = contextToEnv ctx


data PatternDeclaration
  = PHasType String PatternType
  | PHasDef String Term PatternType

instance Show PatternDeclaration where
  show (PHasType x t)  = x ++ " : " ++ show t
  show (PHasDef x v t) = x ++ " = " ++ show v ++ " : " ++ show t

name :: PatternDeclaration -> String
name (PHasType n _)  = n
name (PHasDef n _ _) = n

patternDeclarationToDeclaration :: PatternDeclaration -> Declaration
patternDeclarationToDeclaration (PHasType x t)  = HasType x (patternTypeToType t)
patternDeclarationToDeclaration (PHasDef x v t) = HasDef x v (patternTypeToType t)

declarationToPatternDeclaration :: Declaration -> PatternDeclaration
declarationToPatternDeclaration (HasType x t)  = PHasType x (typeToPatternType t)
declarationToPatternDeclaration (HasDef x v t) = PHasDef x v (typeToPatternType t)

type PatternContext = [PatternDeclaration]

lookupContext :: String -> PatternContext -> Maybe PatternType
lookupContext n [] = Nothing
lookupContext n (PHasType x t : _) | n == x = Just t
lookupContext n (PHasDef x _ t : _) | n == x = Just t
lookupContext n (_ : decls) = lookupContext n decls

patternContextToContext :: PatternContext -> Context
patternContextToContext = map patternDeclarationToDeclaration

contextToPatternContext :: Context -> PatternContext
contextToPatternContext = map declarationToPatternDeclaration


data TCProblem = TCProblem PatternContext Term PatternType

data Equation = Equation PatternType PatternType

type MetaVar = Int

type Substitution = M.Map MetaVar PatternType

type TypeChecker a = StateT (Signature, PatternContext, MetaVar, Substitution) Maybe a

runTypeChecker :: TypeChecker a -> Signature -> PatternContext -> Maybe a
runTypeChecker checker sig ctx
  = fmap fst (runStateT checker (sig,ctx,0,M.empty))
      

failure :: TypeChecker a
failure = StateT (\_ -> Nothing)

signature :: TypeChecker Signature
signature = do (sig,_,_,_) <- get
               return sig

context :: TypeChecker PatternContext
context = do (_,ctx,_,_) <- get
             return ctx

putContext :: PatternContext -> TypeChecker ()
putContext ctx = do (sig,_,nextMeta,subs) <- get
                    put (sig,ctx,nextMeta,subs)

extend :: PatternContext -> TypeChecker a -> TypeChecker a
extend ectx tc = do ctx <- context
                    putContext (ectx++ctx)
                    x <- tc
                    putContext ctx
                    return x

newMetaVar :: TypeChecker PatternType
newMetaVar = do (sig,ctx,nextMeta,subs) <- get
                put (sig,ctx,nextMeta+1,subs)
                return $ PMeta nextMeta

substitution :: TypeChecker Substitution
substitution = do (_,_,_,subs) <- get
                  return subs

putSubstitution :: Substitution -> TypeChecker ()
putSubstitution subs = do (sig,ctx,nextMeta,_) <- get
                          put (sig,ctx,nextMeta,subs)

occurs :: MetaVar -> PatternType -> Bool
occurs x (PTyCon _) = False
occurs x (PFun a b) = occurs x a || occurs x b
occurs x (PMeta y)  = x == y


solve :: [Equation] -> Substitution -> Maybe Substitution
solve [] subs' = return subs'
solve (Equation (PMeta x) t2 : eqs) subs'
  = do guard (not (occurs x t2))
       solve eqs (M.insert x t2 subs')
solve (Equation t1 (PMeta y) : eqs) subs'
  = do guard (not (occurs y t1))
       solve eqs (M.insert y t1 subs')
solve (Equation (PTyCon tycon1) (PTyCon tycon2) : eqs) subs'
  = do guard (tycon1 == tycon2)
       solve eqs subs'
solve (Equation (PFun a1 b1) (PFun a2 b2) : eqs) subs'
  = solve (Equation a1 a2 : Equation b1 b2 : eqs) subs'
solve _ _ = Nothing


addSubstitutions :: Substitution -> TypeChecker ()
addSubstitutions subs'
  = do subs <- substitution
       let subs2 = M.union subs' subs
           subs2' = M.map (substitute subs2) subs2
       putSubstitution subs2'
  where
    substitute :: Substitution -> PatternType -> PatternType
    substitute s (PTyCon tycon) = PTyCon tycon
    substitute s (PFun a b)     = PFun (substitute s a) (substitute s b)
    substitute s (PMeta i)      = case M.lookup i s of
                                    Nothing -> PMeta i
                                    Just t  -> substitute s t


unify :: PatternType -> PatternType -> TypeChecker ()
unify p q = case solve [Equation p q] M.empty of
              Nothing    -> failure
              Just subs' -> addSubstitutions subs'

instantiate :: PatternType -> TypeChecker PatternType
instantiate (PTyCon tycon)     = return $ PTyCon tycon
instantiate (PFun a b)         = do a' <- instantiate a
                                    b' <- instantiate b
                                    return $ PFun a' b'
instantiate (PMeta x)          = do subs <- substitution
                                    return $ fromMaybe (PMeta x) (M.lookup x subs)


typeInContext :: String -> TypeChecker PatternType
typeInContext n = do ctx <- context
                     case lookupContext n ctx of
                       Nothing -> failure
                       Just t  -> return t


hasTypeInContext :: String -> PatternType -> TypeChecker ()
hasTypeInContext n ty = do ctx <- context
                           case lookupContext n ctx of
                             Nothing  -> failure
                             Just ty' -> case solve [Equation ty ty'] M.empty of
                               Nothing    -> failure
                               Just subs' -> addSubstitutions subs'


tyconExists :: String -> TypeChecker ()
tyconExists n = do Signature tycons _ <- signature
                   guard $ n `elem` tycons


typeInSignature :: String -> TypeChecker ConSig
typeInSignature n = do Signature _ consigs <- signature
                       case lookup n consigs of
                         Nothing -> failure
                         Just t  -> return t


isType :: Type -> TypeChecker ()
isType (TyCon tc) = tyconExists tc
isType (Fun a b)  = isType a >> isType b


checkifyConData :: String -> [Term] -> PatternType -> TypeChecker ()
checkifyConData c as ty = do sig <- signature
                             case lookupSignature c sig of
                               Nothing -> failure
                               Just (ConSig args ret) -> do
                                 guard $ length as == length args
                                 unify ty (typeToPatternType ret)
                                 sequence_ $ zipWith (\a ty -> checkify a (typeToPatternType ty)) as args

checkifyPattern :: Pattern -> PatternType -> TypeChecker PatternContext
checkifyPattern (VarPat x) patTy = return [PHasType x patTy]
checkifyPattern (ConPat c ps) patTy
  = do sig <- signature
       case lookupSignature c sig of
         Nothing -> failure
         Just (ConSig args ret) -> do
           guard $ length ps == length args
           unify patTy (typeToPatternType ret)
           rss <- sequence $ zipWith (\p patTy' -> checkifyPattern p (typeToPatternType patTy')) ps args
           return $ concat rss


checkifyClauses :: PatternType -> [Clause] -> PatternType -> TypeChecker ()
checkifyClauses patTy [] ty = return ()
checkifyClauses patTy (Clause pat body:cs) ty
  = do ctx' <- checkifyPattern pat patTy
       extend ctx' (checkify body ty)
       checkifyClauses patTy cs ty


checkify :: Term -> PatternType -> TypeChecker ()
checkify (Var n)     ty = hasTypeInContext n ty
checkify (Ann m ty') ty = do let tyP' = typeToPatternType ty'
                             unify tyP' ty
                             checkify m tyP'
checkify (Lam x m)   ty = do a <- newMetaVar
                             b <- newMetaVar
                             unify ty (PFun a b)
                             a' <- instantiate a
                             b' <- instantiate b
                             extend [PHasType x a'] (checkify m b')
checkify (App f x)   ty = do a <- newMetaVar
                             checkify f (PFun a ty)
                             a' <- instantiate a
                             checkify x a'
checkify (Con c as)  ty = checkifyConData c as ty
checkify (Case m cs) ty = do ty' <- newMetaVar
                             checkify m ty'
                             ty2' <- instantiate ty'
                             checkifyClauses ty2' cs ty


-- type checking succees exactly when checkification succeeds
-- and there is a substitution for every meta-variable

metasSolved :: TypeChecker ()
metasSolved = do (_,_,nextMeta,subs) <- get
                 guard $ nextMeta == M.size subs

check :: Term -> PatternType -> TypeChecker ()
check m ty = do checkify m ty
                metasSolved
                
infer :: Term -> TypeChecker PatternType
infer m = do ty <- newMetaVar
             checkify m ty
             metasSolved
             instantiate ty