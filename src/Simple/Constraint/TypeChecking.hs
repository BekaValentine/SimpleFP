{-# LANGUAGE RecursiveDo #-}

module Simple.Constraint.TypeChecking where

import System.IO.Unsafe

import Control.Applicative ((<$>))
import Control.Monad (guard,forM)
import Control.Monad.Trans.State
import Data.List (intercalate,nub)
import Data.Maybe (fromMaybe,fromJust)

import Simple.Core.Term
import Simple.Core.Type
import Simple.Core.Evaluation



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



-- Unifying Type Checkers

data Equation = Equation PatternType PatternType

type MetaVar = Int

type Substitution = [(MetaVar,PatternType)]

type TypeChecker a = StateT (Signature, PatternContext, MetaVar, Substitution) Maybe a

runTypeChecker :: TypeChecker a -> Signature -> PatternContext -> Maybe a
runTypeChecker checker sig ctx
  = fmap fst (runStateT checker (sig,ctx,0,[]))
      

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


solve :: [Equation] -> Maybe Substitution
solve eqs = go eqs []
  where
    go [] subs' = return subs'
    go (Equation (PMeta x) t2 : eqs) subs'
      = do guard (not (occurs x t2))
           go eqs ((x,t2):subs')
    go (Equation t1 (PMeta y) : eqs) subs'
      = do guard (not (occurs y t1))
           go eqs ((y,t1):subs')
    go (Equation (PTyCon tycon1) (PTyCon tycon2) : eqs) subs'
      = do guard (tycon1 == tycon2)
           go eqs subs'
    go (Equation (PFun a1 b1) (PFun a2 b2) : eqs) subs'
      = go (Equation a1 a2 : Equation b1 b2 : eqs) subs'
    go _ _ = Nothing


addSubstitutions :: Substitution -> TypeChecker ()
addSubstitutions subs'
  = do completeSubstitution subs'
       substituteContext
  where
    
    completeSubstitution subs'
      = do subs <- substitution
           let subs2 = subs' ++ subs
               subs2' = map (\(k,v) -> (k,substitute subs2 v)) subs2
           return subs2'
    
    substitute :: Substitution -> PatternType -> PatternType
    substitute s (PTyCon tycon) = PTyCon tycon
    substitute s (PFun a b)     = PFun (substitute s a) (substitute s b)
    substitute s (PMeta i)      = case lookup i s of
                                    Nothing -> PMeta i
                                    Just t  -> substitute s t
    
    substituteContext
      = do ctx <- context
           ctx' <- forM ctx $ \d ->
                     case d of
                       PHasType x t  -> PHasType x <$> instantiate t
                       PHasDef x v t -> PHasDef x v <$> instantiate t
           putContext ctx'


unify :: PatternType -> PatternType -> TypeChecker ()
unify p q = case solve [Equation p q] of
              Nothing    -> failure
              Just subs' -> addSubstitutions subs'

instantiate :: PatternType -> TypeChecker PatternType
instantiate (PTyCon tycon)     = return $ PTyCon tycon
instantiate (PFun a b)         = do a' <- instantiate a
                                    b' <- instantiate b
                                    return $ PFun a' b'
instantiate (PMeta x)          = do subs <- substitution
                                    return $ fromMaybe (PMeta x) (lookup x subs)



typeInContext :: String -> TypeChecker PatternType
typeInContext n = do ctx <- context
                     case lookupContext n ctx of
                       Nothing -> failure
                       Just t  -> return t

typeInSignature :: String -> TypeChecker ConSig
typeInSignature n = do Signature _ consigs <- signature
                       case lookup n consigs of
                         Nothing -> failure
                         Just t  -> return t

tyconExists :: String -> TypeChecker ()
tyconExists n = do Signature tycons _ <- signature
                   guard $ n `elem` tycons



-- Type well-formedness

isType :: Type -> TypeChecker ()
isType (TyCon tc) = tyconExists tc
isType (Fun a b)  = isType a >> isType b



-- Type Inference

inferify :: Term -> TypeChecker PatternType
inferify (Var x)     = typeInContext x
inferify (Ann m t)   = do let pt = typeToPatternType t
                          checkify m pt
                          return pt
inferify (Lam x b)   = do arg <- newMetaVar
                          ret <- extend [PHasType x arg]
                                      $ inferify b
                          arg' <- instantiate arg
                          return $ PFun arg ret
inferify (App f a)   = do PFun arg ret <- inferify f
                          checkify a arg
                          return ret
inferify (Con c as)  = do ConSig args ret <- typeInSignature c
                          let args' = map typeToPatternType args
                              ret' = typeToPatternType ret
                          guard $ length as == length args'
                          checkifyMulti as args'
                          return ret'
  where
    checkifyMulti :: [Term] -> [PatternType] -> TypeChecker ()
    checkifyMulti []     []     = return ()
    checkifyMulti (m:ms) (t:ts) = do t' <- instantiate t
                                     checkify m t'
                                     checkifyMulti ms ts
    checkifyMulti _      _      = failure
inferify (Case m cs) = do t <- inferify m
                          t' <- inferifyClauses t cs
                          return t'

inferifyClause :: PatternType -> Clause -> TypeChecker PatternType
inferifyClause patTy (Clause p b) = do ctx' <- checkifyPattern p patTy
                                       ctx <- context
                                       extend ctx'
                                            $ inferify b


inferifyClauses :: PatternType -> [Clause] -> TypeChecker PatternType
inferifyClauses patTy cs = do ts <- sequence $ map (inferifyClause patTy) cs
                              case ts of
                                t:ts -> do
                                  sequence_ (map (unify t) ts)
                                  t' <- instantiate t
                                  return t'
                                _ -> failure



-- Type Checking

checkify :: Term -> PatternType -> TypeChecker ()
checkify (Var x)     t = do t' <- inferify (Var x)
                            unify t t'
checkify (Ann m t')  t = do let pt' = typeToPatternType t'
                            unify t pt'
                            pt2' <- instantiate pt'
                            checkify m pt2'
checkify (Lam x b)   t = do arg <- newMetaVar
                            ret <- newMetaVar
                            unify t (PFun arg ret)
                            arg' <- instantiate arg
                            ret' <- instantiate ret
                            extend [PHasType x arg']
                                 $ checkify b ret'
checkify (App f a)   t = do arg <- newMetaVar
                            checkify f (PFun arg t)
                            arg' <- instantiate arg
                            checkify a arg'
checkify (Con c as)  t = do t' <- inferify (Con c as)
                            unify t t'
checkify (Case m cs) t = do t' <- inferify m
                            checkifyClauses t' cs t

checkifyPattern :: Pattern -> PatternType -> TypeChecker PatternContext
checkifyPattern patTy t = do ctx <- go patTy t
                             let names = map name ctx
                             guard $ length names == length (nub names)
                             return ctx
  where
    go (VarPat x)    t = return [PHasType x t]
    go (ConPat c ps) t = do ConSig args ret <- typeInSignature c
                            let args' = map typeToPatternType args
                                ret' = typeToPatternType ret
                            guard $ length ps == length args'
                            unify t ret'
                            rss <- goMulti ps args'
                            return $ concat rss
    
    goMulti []     []     = return []
    goMulti (p:ps) (t:ts) = do t' <- instantiate t
                               ctx <- go p t
                               ctxs <- goMulti ps ts
                               return (ctx:ctxs)
    goMulti _      _      = failure


checkifyClauses :: PatternType -> [Clause] -> PatternType -> TypeChecker ()
checkifyClauses patTy [] t = return ()
checkifyClauses patTy (Clause p b:cs) t = do ctx' <- checkifyPattern p patTy
                                             ctx <- context
                                             extend ctx'
                                                  $ checkify b t
                                             checkifyClauses patTy cs t



-- type checking succees exactly when checkification succeeds
-- and there is a substitution for every meta-variable

metasSolved :: TypeChecker ()
metasSolved = do (_,_,nextMeta,subs) <- get
                 guard $ nextMeta == length subs

check :: Term -> PatternType -> TypeChecker ()
check m t = do checkify m t
               metasSolved
                
infer :: Term -> TypeChecker PatternType
infer m = do t <- inferify m
             metasSolved
             instantiate t