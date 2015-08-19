{-# LANGUAGE RecursiveDo #-}
{-# OPTIONS -Wall #-}

module Poly.Constraint.TypeChecking where

import System.IO.Unsafe

import Control.Applicative ((<$>))
import Control.Monad (guard,forM)
import Control.Monad.Trans.State
import Data.List (intercalate,nub)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)

import Poly.Core.Term
import Poly.Core.Type
import Poly.Core.Evaluation




rawPatternToPattern :: Pattern -> Pattern
rawPatternToPattern (VarPat x) = VarPat x
rawPatternToPattern (ConPat c as) = ConPat c (map rawPatternToPattern as)

freshen :: [String] -> String -> String
freshen xs x
  | x `elem` xs = freshen xs (x ++ "'")
  | otherwise   = x


-- Signatures

-- params, arg types, return type
data ConSig = ConSig [String] [Type] Type

instance Show ConSig where
  show (ConSig [] as r) = "(" ++ intercalate "," (map show as) ++ ")" ++ show r
  show (ConSig params as r) = "forall " ++ intercalate " " params ++ ". (" ++ intercalate "," (map show as) ++ ")" ++ show r

data TyConSig = TyConSig Int

instance Show TyConSig where
  show (TyConSig 0) = "*"
  show (TyConSig n) = "(" ++ intercalate "," (replicate n "*") ++ ") -> *"

data Signature = Signature [(String,TyConSig)] [(String,ConSig)]

instance Show Signature where
  show (Signature tyconsigs consigs)
    = "Types:\n" ++
        unlines [ "  " ++ c ++ " :: " ++ show tyconsig
                | (c,tyconsig) <- tyconsigs
                ] ++
      "Constructors:\n" ++
        unlines [ "  " ++ c ++ " :: " ++ show consig
                | (c,consig) <- consigs
                ]

lookupSignature :: String -> Signature -> Maybe ConSig
lookupSignature c (Signature _ consigs) = lookup c consigs



-- Pattern Types
 
data PatternType
  = PTyCon String [PatternType]
  | PFun PatternType PatternType
  | PMeta Int
  | PTyVar String
  | PForall String PatternType
  deriving (Eq,Show)

typeToPatternType :: Type -> PatternType
typeToPatternType (TyCon tycon args) = PTyCon tycon (map typeToPatternType args)
typeToPatternType (Fun a b)          = PFun (typeToPatternType a) (typeToPatternType b)
typeToPatternType (TyVar x)          = PTyVar x
typeToPatternType (Forall x b)       = PForall x (typeToPatternType b)

patternTypeToType :: PatternType -> Type
patternTypeToType (PTyCon tycon args) = TyCon tycon (map patternTypeToType args)
patternTypeToType (PFun a b)          = Fun (patternTypeToType a) (patternTypeToType b)
patternTypeToType (PTyVar x)          = TyVar x
patternTypeToType (PForall x b)       = Forall x (patternTypeToType b)
patternTypeToType (PMeta _)           = error "Cannot convert metavars to types."

substituteType :: [String] -> PatternType -> String -> PatternType -> PatternType
substituteType tyctx t x (PTyCon tycon args) = PTyCon tycon (map (substituteType tyctx t x) args)
substituteType tyctx t x (PFun arg ret)      = PFun (substituteType tyctx t x arg) (substituteType tyctx t x ret)
substituteType _     _ _ (PMeta y)           = PMeta y
substituteType _     t x (PTyVar y)          = if x == y
                                               then t
                                               else PTyVar y
substituteType tyctx t x (PForall y b)       = if x == y
                                               then PForall y b
                                               else let y' = freshen tyctx y
                                                        b' = substituteType tyctx (PTyVar y') y b
                                                    in PForall y' (substituteType (y':tyctx) t x b')


-- Contexts

data Declaration
  = HasType String Type
  | HasDef String Term Type
  | IsType String

instance Show Declaration where
  show (HasType x t)  = x ++ " : " ++ show t
  show (HasDef x v t) = x ++ " = " ++ show v ++ " : " ++ show t
  show (IsType x)     = x ++ " type"

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
  | PIsType String

instance Show PatternDeclaration where
  show (PHasType x t)  = x ++ " : " ++ show t
  show (PHasDef x v t) = x ++ " = " ++ show v ++ " : " ++ show t
  show (PIsType x)     = x ++ " type"

name :: PatternDeclaration -> String
name (PHasType n _)  = n
name (PHasDef n _ _) = n
name (PIsType _)     = error "IsType declarations do not have names."

patternDeclarationToDeclaration :: PatternDeclaration -> Declaration
patternDeclarationToDeclaration (PHasType x t)  = HasType x (patternTypeToType t)
patternDeclarationToDeclaration (PHasDef x v t) = HasDef x v (patternTypeToType t)
patternDeclarationToDeclaration (PIsType x)     = IsType x

declarationToPatternDeclaration :: Declaration -> PatternDeclaration
declarationToPatternDeclaration (HasType x t)  = PHasType x (typeToPatternType t)
declarationToPatternDeclaration (HasDef x v t) = PHasDef x v (typeToPatternType t)
declarationToPatternDeclaration (IsType x)     = PIsType x

type PatternContext = [PatternDeclaration]

lookupContext :: String -> PatternContext -> Maybe PatternType
lookupContext _ [] = Nothing
lookupContext n (PHasType x t : _) | n == x = Just t
lookupContext n (PHasDef x _ t : _) | n == x = Just t
lookupContext n (_ : decls) = lookupContext n decls

patternContextToContext :: PatternContext -> Context
patternContextToContext = map patternDeclarationToDeclaration

contextToPatternContext :: Context -> PatternContext
contextToPatternContext = map declarationToPatternDeclaration



-- Unifying Type Checkers

data Equation = Equation PatternType PatternType

type TyVarCount = Int

type MetaVar = Int

type Substitution = M.Map MetaVar PatternType

type TypeChecker a = StateT (Signature, PatternContext, TyVarCount, MetaVar, Substitution) Maybe a

runTypeChecker :: TypeChecker a -> Signature -> PatternContext -> Maybe a
runTypeChecker checker sig ctx
  = fmap fst (runStateT checker (sig,ctx,0,0,M.empty))
      

failure :: TypeChecker a
failure = StateT (\_ -> Nothing)

signature :: TypeChecker Signature
signature = do (sig,_,_,_,_) <- get
               return sig

context :: TypeChecker PatternContext
context = do (_,ctx,_,_,_) <- get
             return ctx

putContext :: PatternContext -> TypeChecker ()
putContext ctx = do (sig,_,tyvar,nextMeta,subs) <- get
                    put (sig,ctx,tyvar,nextMeta,subs)

extend :: PatternContext -> TypeChecker a -> TypeChecker a
extend ectx tc = do ctx <- context
                    putContext (ectx++ctx)
                    x <- tc
                    putContext ctx
                    return x

newTyVar :: TypeChecker String
newTyVar = do (sig,ctx,tyvar,nextMeta,subs) <- get
              put (sig,ctx,tyvar+1,nextMeta,subs)
              return $ "t" ++ show tyvar

newMetaVar :: TypeChecker PatternType
newMetaVar = do (sig,ctx,tyvar,nextMeta,subs) <- get
                put (sig,ctx,tyvar,nextMeta+1,subs)
                return $ PMeta nextMeta

substitution :: TypeChecker Substitution
substitution = do (_,_,_,_,subs) <- get
                  return subs

putSubstitution :: Substitution -> TypeChecker ()
putSubstitution subs = do (sig,ctx,tyvar,nextMeta,_) <- get
                          put (sig,ctx,tyvar,nextMeta,subs)

occurs :: MetaVar -> PatternType -> Bool
occurs x (PTyCon _ args) = any (occurs x) args
occurs x (PFun a b)      = occurs x a || occurs x b
occurs x (PMeta y)       = x == y
occurs _ (PTyVar _)      = False
occurs x (PForall _ b)   = occurs x b


solve :: [Equation] -> Maybe Substitution
solve eqs0 = go eqs0 M.empty
  where
    go [] subs' = return subs'
    go (Equation (PMeta x) t2 : eqs) subs'
      = do guard (not (occurs x t2))
           go eqs (M.insert x t2 subs')
    go (Equation t1 (PMeta y) : eqs) subs'
      = do guard (not (occurs y t1))
           go eqs (M.insert y t1 subs')
    go (Equation (PTyCon tycon1 args1) (PTyCon tycon2 args2) : eqs) subs'
      = do guard $ tycon1 == tycon2 && length args1 == length args2
           go (zipWith Equation args1 args2 ++ eqs) subs'
    go (Equation (PFun a1 b1) (PFun a2 b2) : eqs) subs'
      = go (Equation a1 a2 : Equation b1 b2 : eqs) subs'
    go (Equation (PTyVar x) (PTyVar y) : eqs) subs'
      = do guard (x == y)
           go eqs subs'
    go (Equation (PForall x b) (PForall y b') : eqs) subs'
      = let b2' = substituteType [] (PTyVar x) y b'
        in go (Equation b b2' : eqs) subs'
    go _ _ = Nothing


addSubstitutions :: Substitution -> TypeChecker ()
addSubstitutions subs0
  = do completeSubstitution subs0
       substituteContext
  where
    
    completeSubstitution subs'
      = do subs <- substitution
           let subs2 = M.union subs' subs
               subs2' = M.map (substitute subs2) subs2
           putSubstitution subs2'
    
    substitute :: Substitution -> PatternType -> PatternType
    substitute s (PTyCon tycon args) = PTyCon tycon (map (substitute s) args)
    substitute s (PFun a b)          = PFun (substitute s a) (substitute s b)
    substitute s (PMeta i)           = case M.lookup i s of
                                         Nothing -> PMeta i
                                         Just t  -> substitute s t
    substitute _ (PTyVar x)          = PTyVar x
    substitute s (PForall x b)       = PForall x (substitute s b)
    
    substituteContext
      = do ctx <- context
           ctx' <- forM ctx $ \d ->
                     case d of
                       PHasType x t  -> PHasType x <$> instantiate t
                       PHasDef x v t -> PHasDef x v <$> instantiate t
                       PIsType t     -> return $ PIsType t
           putContext ctx'


unify :: PatternType -> PatternType -> TypeChecker ()
unify p q = case solve [Equation p q] of
              Nothing    -> failure
              Just subs' -> addSubstitutions subs'

instantiate :: PatternType -> TypeChecker PatternType
instantiate (PTyCon tycon args) = do args' <- sequence (map instantiate args)
                                     return $ PTyCon tycon args'
instantiate (PFun a b)          = do a' <- instantiate a
                                     b' <- instantiate b
                                     return $ PFun a' b'
instantiate (PMeta x)           = do subs <- substitution
                                     return $ fromMaybe (PMeta x) (M.lookup x subs)
instantiate (PTyVar x)          = return $ PTyVar x
instantiate (PForall x b)       = do b' <- instantiate b
                                     return $ PForall x b'



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

tyconExists :: String -> TypeChecker Int
tyconExists n = do Signature tyconsigs _ <- signature
                   let matches = filter (\(tycon,_) -> n == tycon) tyconsigs
                   case matches of
                     [(_,TyConSig arity)] -> return arity
                     _ -> failure



-- Type well-formedness

isType :: [String] -> Type -> TypeChecker ()
isType vars (TyCon tc args) = do n <- tyconExists tc
                                 guard $ n == length args
                                 sequence_ (map (isType vars) args)
isType vars (Fun a b)       = isType vars a >> isType vars b
isType vars (TyVar x)       = guard (x `elem` vars)
isType vars (Forall x s)    = let x' = freshen vars x
                              in isType (x':vars) (subst vars (TyVar x') x s)
  where
    subst :: [String] -> Type -> String -> Type -> Type
    subst ctx t _ (TyCon c as) = TyCon c (map (subst ctx t c) as)
    subst ctx t v (Fun a b)    = Fun (subst ctx t v a) (subst ctx t v b)
    subst _   t v (TyVar y)    = if v == y then t else TyVar y
    subst ctx t v (Forall y b) = let y' = freshen ctx y
                                     b' = subst ctx (TyVar y') y b
                                 in Forall y' (subst ctx t v b')



-- Inserting param variables into con data

instantiateParams :: [String] -> [PatternType] -> PatternType -> TypeChecker ([PatternType],PatternType)
instantiateParams params args ret = go [] params
  where
    go :: [(String,PatternType)] -> [String] -> TypeChecker ([PatternType],PatternType)
    go subs []     = do let args' = map (subMulti subs) args
                            ret' = subMulti subs ret
                        return (args',ret')
    go subs (p:ps) = do v <- newMetaVar
                        go ((p,v):subs) ps
    
    subMulti :: [(String,PatternType)] -> PatternType -> PatternType
    subMulti []             ty = ty
    subMulti ((x,ty'):subs) ty = subMulti subs (substituteType [] ty' x ty)


-- Instantiating quantified values until there are no more initial quantifiers
instantiateQuantifiers :: PatternType -> TypeChecker PatternType
instantiateQuantifiers (PForall x b) = do m <- newMetaVar
                                          let b' = substituteType [] m x b
                                          instantiateQuantifiers b'
instantiateQuantifiers t = return t

{-
do ctx <- context
                              x' <- newTyVar
                              let tyvars = [ n | PIsType n <- ctx ]
                                  b' = substituteType tyvars (PTyVar x') x b
                              m' <- extend [PIsType x']
                                         $ checkify m b'
                              return m'
-}

-- Type Inference

inferify :: Term -> TypeChecker PatternType
inferify (Var x)     = typeInContext x
inferify (Ann m t)   = do let pt = typeToPatternType t
                          checkify m pt
                          pt' <- instantiate pt
                          return pt'
inferify (Lam x b)   = do arg <- newMetaVar
                          ret <- extend [PHasType x arg]
                                      $ inferify b
                          arg' <- instantiate arg
                          return $ PFun arg' ret
inferify (App f a)   = do t <- inferify f
                          PFun arg ret <- instantiateQuantifiers t
                          checkify a arg
                          ret' <- instantiate ret
                          return ret'
inferify (Con c as)  = do ConSig params args ret <- typeInSignature c
                          (args',ret') <- instantiateParams
                                            params
                                            (map typeToPatternType args)
                                            (typeToPatternType ret)
                          guard $ length as == length args'
                          checkifyMulti as args'
                          ret'' <- instantiate ret'
                          return ret''
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
                                       t <- extend ctx'
                                                 $ inferify b
                                       return t


inferifyClauses :: PatternType -> [Clause] -> TypeChecker PatternType
inferifyClauses patTy cs = do ts <- sequence $ map (inferifyClause patTy) cs
                              case ts of
                                t:ts' -> do
                                  sequence_ (map (unify t) ts')
                                  t' <- instantiate t
                                  return t'
                                _ -> failure



-- Type Checking

checkify :: Term -> PatternType -> TypeChecker ()
checkify m (PForall x b) = do ctx <- context
                              x' <- newTyVar
                              let tyvars = [ n | PIsType n <- ctx ]
                                  b' = substituteType tyvars (PTyVar x') x b
                              m' <- extend [PIsType x']
                                         $ checkify m b'
                              return m'
checkify (Var x)     t   = do t' <- inferify (Var x)
                              equivQuantifiers t' t
checkify (Ann m t')  t   = do let pt' = typeToPatternType t'
                              unify t pt'
                              pt'' <- instantiate pt'
                              checkify m pt''
checkify (Lam x b)   t   = do arg <- newMetaVar
                              ret <- newMetaVar
                              unify t (PFun arg ret)
                              arg' <- instantiate arg
                              ret' <- instantiate ret
                              extend [PHasType x arg']
                                   $ checkify b ret'
checkify (App f a)   t   = do arg <- newMetaVar
                              checkify f (PFun arg t)
                              arg' <- instantiate arg
                              checkify a arg'
checkify (Con c as)  t   = do t' <- inferify (Con c as)
                              unify t t'
checkify (Case m cs) t   = do t' <- inferify m
                              checkifyClauses t' cs t

equivQuantifiers :: PatternType -> PatternType -> TypeChecker ()
equivQuantifiers t (PForall x' b')
  = do x2' <- newTyVar
       ctx <- context
       let tyvars = [ n | PIsType n <- ctx ]
           b2' = substituteType tyvars (PTyVar x2') x' b'
       -- m' <- equivQuantifiers m t b2'
       -- return (TyLam x2' m')
       equivQuantifiers t b2'
equivQuantifiers (PForall x b) t'
  = do x2 <- newMetaVar
       ctx <- context
       let tyvars = [ n | PIsType n <- ctx ]
           b2 = substituteType tyvars x2 x b
       --etaQuantifiers (TyApp m x2) b2 t'
       equivQuantifiers b2 t'
equivQuantifiers (PFun arg ret) (PFun arg' ret')
  = do --unify arg arg'
       equivQuantifiers arg' arg
       equivQuantifiers ret ret'
equivQuantifiers t t'
  = unify t t'

checkifyPattern :: Pattern -> PatternType -> TypeChecker PatternContext
checkifyPattern pat t0
  = do ctx <- go pat t0
       let names = map name ctx
       guard $ length names == length (nub names)
       return ctx
  where
    go (VarPat x) t
      = return [PHasType x t]
    go (ConPat c ps) t
      = do ConSig params args ret <- typeInSignature c
           (args',ret') <- instantiateParams
                             params
                             (map typeToPatternType args)
                             (typeToPatternType ret)
           guard $ length ps == length args'
           unify t ret'
           rss <- goMulti ps args'
           return $ concat rss
    
    goMulti []     []     = return []
    goMulti (p:ps) (t:ts) = do t' <- instantiate t
                               ctx <- go p t'
                               ctxs <- goMulti ps ts
                               return (ctx:ctxs)
    goMulti _      _      = failure


checkifyClauses :: PatternType -> [Clause] -> PatternType -> TypeChecker ()
checkifyClauses _ [] _ = return ()
checkifyClauses patTy (Clause p b:cs) t
  = do ctx' <- checkifyPattern p patTy
       extend ctx'
            $ checkify b t
       patTy' <- instantiate patTy
       t' <- instantiate t
       checkifyClauses patTy' cs t'



-- type checking succees exactly when checkification succeeds
-- and there is a substitution for every meta-variable

metasSolved :: TypeChecker ()
metasSolved = do (_,_,_,nextMeta,subs) <- get
                 guard $ nextMeta == M.size subs

check :: Term -> PatternType -> TypeChecker ()
check m t = do checkify m t
               metasSolved
                
infer :: Term -> TypeChecker PatternType
infer m = do t <- inferify m
             metasSolved
             t' <- instantiate t
             return t'