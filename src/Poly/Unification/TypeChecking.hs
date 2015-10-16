{-# OPTIONS -Wall #-}
{-# LANGUAGE TypeFamilies #-}

module Poly.Unification.TypeChecking where

import Control.Applicative ((<$>))
import Control.Monad.Except
import Control.Monad.State
import Data.List (intercalate,nubBy,find)

import Scope
import TypeChecker
import Poly.Core.Term
import Poly.Core.Type




-- Signatures

-- argnum, Params -> ([Arg],Ret)
data ConSig = ConSig Int (Scope Type ([Type],Type))

instance Show ConSig where
  show (ConSig n sc)
    = let (as,r) = instantiate sc [ TyVar (TyGenerated i) | i <- [0..n] ]
      in "(" ++ intercalate "," (map show as) ++ ")" ++ show r

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




-- Definitions

type Definitions = [(String,Term,Type)]




-- Contexts

type Context = [(Int,Type)]

type TyVarContext = [Int]




-- Unifying Type Checkers

data Equation = Equation Type Type

type MetaVar = Int

type Substitution = [(MetaVar,Type)]

data TCState
  = TCState
    { tcSig :: Signature
    , tcDefs :: Definitions
    , tcCtx :: Context
    , tcTyVarCtx :: TyVarContext
    , tcNextName :: Int
    , tcNextMeta :: MetaVar
    , tcSubs :: Substitution
    }

instance TypeCheckerState TCState where
  type Sig TCState = Signature
  type Defs TCState = Definitions
  type Ctx TCState = Context
  typeCheckerSig = tcSig
  putTypeCheckerSig s sig = s { tcSig = sig }
  typeCheckerDefs = tcDefs
  putTypeCheckerDefs s defs = s { tcDefs = defs }
  addTypeCheckerDefs s edefs = s { tcDefs = edefs ++ tcDefs s }
  typeCheckerCtx = tcCtx
  putTypeCheckerCtx s ctx = s { tcCtx = ctx }
  addTypeCheckerCtx s ectx = s { tcCtx = ectx ++ tcCtx s }
  typeCheckerNextName = tcNextName
  putTypeCheckerNextName s n = s { tcNextName = n }

instance TypeCheckerMetas TCState where
  type Subs TCState = Substitution
  typeCheckerNextMeta = tcNextMeta
  putTypeCheckerNextMeta s n = s { tcNextMeta = n }
  typeCheckerSubs = tcSubs
  putTypeCheckerSubs s subs = s { tcSubs = subs }

type TypeChecker a = StateT TCState (Either String) a

runTypeChecker :: TypeChecker a -> Signature -> Definitions -> Context -> Int -> Either String (a,TCState)
runTypeChecker checker sig defs ctx i
  = runStateT checker (TCState sig defs ctx [] i 0 [])
      

tyVarContext :: TypeChecker TyVarContext
tyVarContext = tcTyVarCtx <$> get

putTyVarContext :: TyVarContext -> TypeChecker ()
putTyVarContext tyVarCtx = do s <- get
                              put (s { tcTyVarCtx = tyVarCtx })

extendTyVarContext :: TyVarContext -> TypeChecker a -> TypeChecker a
extendTyVarContext etyVarCtx tc = do tyVarCtx <- tyVarContext
                                     putTyVarContext (etyVarCtx ++ tyVarCtx)
                                     x <- tc
                                     putTyVarContext tyVarCtx
                                     return x

occurs :: MetaVar -> Type -> Bool
occurs x (TyCon _ args) = any (occurs x) args
occurs x (Fun a b)      = occurs x a || occurs x b
occurs x (Meta y)       = x == y
occurs _ (TyVar _)      = False
occurs x (Forall sc)    = occurs x (instantiate sc (repeat (TyVar undefined)))


solve :: [Equation] -> TypeChecker Substitution
solve eqs0 = go eqs0 []
  where
    go :: [Equation] -> Substitution -> TypeChecker Substitution
    go [] subs' = return subs'
    go (Equation (Meta x) (Meta y) : eqs) subs' | x == y
      = go eqs subs'
    go (Equation (Meta x) t2 : eqs) subs'
      = do unless (not (occurs x t2))
             $ throwError $ "Cannot unify because " ++ show (Meta x)
                         ++ " occurs in " ++ show t2
           go eqs ((x,t2):subs')
    go (Equation t1 (Meta y) : eqs) subs'
      = do unless (not (occurs y t1))
             $ throwError $ "Cannot unify because " ++ show (Meta y)
                         ++ " occurs in " ++ show t1
           go eqs ((y,t1):subs')
    go (Equation (TyCon tycon1 args1) (TyCon tycon2 args2) : eqs) subs'
      = do unless (tycon1 == tycon2)
             $ throwError $ "Mismatching type constructors " ++ tycon1 ++ " and " ++ tycon2
           let largs1 = length args1
               largs2 = length args2
           unless (largs1 == largs2)
             $ throwError $ "Mismatching type constructor arg lengths between "
                         ++ show (TyCon tycon1 args1) ++ " and "
                         ++ show (TyCon tycon2 args2)
           go (zipWith Equation args1 args2 ++ eqs) subs'
    go (Equation (Fun a1 b1) (Fun a2 b2) : eqs) subs'
      = go (Equation a1 a2 : Equation b1 b2 : eqs) subs'
    go (Equation (TyVar x) (TyVar y) : eqs) subs'
      = do unless (x == y)
             $ throwError $ "Cannot unify type variables " ++ show (TyVar x)
            ++ " and " ++ show (TyVar y)
           go eqs subs'
    go (Equation (Forall sc) (Forall sc') : eqs) subs'
      = do i <- newName
           let b = instantiate sc [TyVar (TyGenerated i)]
               b' = instantiate sc' [TyVar (TyGenerated i)]
           go (Equation b b' : eqs) subs'
    go (Equation l r : _) _
      = throwError $ "Cannot unify " ++ show l ++ " with " ++ show r


addSubstitutions :: Substitution -> TypeChecker ()
addSubstitutions subs0
  = do completeSubstitution subs0
       substituteContext
  where
    
    completeSubstitution subs'
      = do subs <- substitution
           let subs2 = subs' ++ subs
               subs2' = nubBy (\(a,_) (b,_) -> a == b) (map (\(k,v) -> (k, instantiateMetas subs2 v)) subs2)
           putSubstitution subs2'
    
    substituteContext
      = do ctx <- context
           subs2 <- substitution
           putContext (map (\(x,t) -> (x,instantiateMetas subs2 t)) ctx)


unify :: Type -> Type -> TypeChecker ()
unify p q = do subs' <- solve [Equation p q]
               addSubstitutions subs'

instantiateMetas :: Substitution -> Type -> Type
instantiateMetas subs (TyCon tycon args)
  = TyCon tycon (map (instantiateMetas subs) args)
instantiateMetas subs (Fun a b)
  = Fun (instantiateMetas subs a) (instantiateMetas subs b)
instantiateMetas subs (Meta i)
  = case lookup i subs of
      Nothing -> Meta i
      Just t  -> instantiateMetas subs t
instantiateMetas _ (TyVar x)
  = TyVar x
instantiateMetas subs (Forall sc)
  = Forall (instantiateMetas subs <$> sc)


typeInContext :: Int -> TypeChecker Type
typeInContext i
  = do ctx <- context
       case lookup i ctx of
         Nothing -> throwError "Unbound automatically generated variable."
         Just t  -> return t

typeInDefinitions :: String -> TypeChecker Type
typeInDefinitions n
  = do defs <- definitions
       case find (\(n',_,_) -> n' == n) defs of
         Nothing      -> throwError $ "Unknown constant/defined term: " ++ n
         Just (_,_,t) -> return t

typeInSignature :: String -> TypeChecker ConSig
typeInSignature n
  = do Signature _ consigs <- signature
       case lookup n consigs of
         Nothing -> throwError $ "Unknown constructor: " ++ n
         Just t  -> return t

tyconExists :: String -> TypeChecker Int
tyconExists n
  = do Signature tyconsigs _ <- signature
       let matches = filter (\(tycon,_) -> n == tycon) tyconsigs
       case matches of
         [(_,TyConSig arity)] -> return arity
         _ -> throwError $ "Unknown type constructor: " ++ n



-- Type well-formedness

isType :: Type -> TypeChecker ()
isType (Meta _)     = return ()
isType (TyCon c as) = do n <- tyconExists c
                         let las = length as
                         unless (n == las)
                           $ throwError $ c ++ " expects " ++ show n ++ " "
                                       ++ (if n == 1 then "arg" else "args")
                                       ++ " but was given " ++ show las
                         mapM_ isType as
isType (Fun a b)    = isType a >> isType b
isType (TyVar _)    = return ()
isType (Forall sc)  = do i <- newName
                         isType (instantiate sc [TyVar (TyGenerated i)])


-- Inserting param variables into con data

instantiateParams :: Int -> Scope Type ([Type],Type) -> TypeChecker ([Type],Type)
instantiateParams n sc
  = do ms <- replicateM n (fmap Meta newMetaVar)
       return $ instantiate sc ms



-- Instantiating quantified values until there are no more initial quantifiers
instantiateQuantifiers :: Type -> TypeChecker Type
instantiateQuantifiers (Forall sc)
  = do meta <- newMetaVar
       let m = Meta meta
       instantiateQuantifiers (instantiate sc [m])
instantiateQuantifiers t = return t



-- Type Inference

inferify :: Term -> TypeChecker Type
inferify (Var (Name x))
  = typeInDefinitions x
inferify (Var (Generated i))
  = typeInContext i
inferify (Ann m t)
  = do isType t
       checkify m t
       subs <- substitution
       return $ instantiateMetas subs t
inferify (Lam sc)
  = do i <- newName
       meta <- newMetaVar
       let arg = Meta meta
       ret <- extendContext [(i,arg)]
                $ inferify (instantiate sc [Var (Generated i)])
       subs <- substitution
       return $ Fun (instantiateMetas subs arg) ret
inferify (App f a)
  = do t <- inferify f
       Fun arg ret <- instantiateQuantifiers t
       checkify a arg
       subs <- substitution
       return $ instantiateMetas subs ret
inferify (Con c as)
  = do ConSig n sc <- typeInSignature c
       (args',ret') <- instantiateParams n sc
       let las = length as
           largs' = length args'
       unless (las == largs')
         $ throwError $ c ++ " expects " ++ show largs' ++ " "
                   ++ (if largs' == 1 then "arg" else "args")
                   ++ " but was given " ++ show las
       checkifyMulti as args'
       subs <- substitution
       return $ instantiateMetas subs ret'
  where
    checkifyMulti :: [Term] -> [Type] -> TypeChecker ()
    checkifyMulti []     []     = return ()
    checkifyMulti (m:ms) (t:ts) = do subs <- substitution
                                     checkify m (instantiateMetas subs t)
                                     checkifyMulti ms ts
    checkifyMulti _      _      = throwError "Mismatched constructor signature lengths."
inferify (Case m cs)
  = do t <- inferify m
       inferifyClauses t cs

inferifyClause :: Type -> Clause -> TypeChecker Type
inferifyClause patTy (Clause p sc)
  = do ctx' <- checkifyPattern p patTy
       let xs = [ Var (Generated i) | (i,_) <- ctx' ]
       extendContext ctx'
         $ inferify (instantiate sc xs)


inferifyClauses :: Type -> [Clause] -> TypeChecker Type
inferifyClauses patTy cs
  = do ts <- mapM (inferifyClause patTy) cs
       case ts of
         [] -> throwError "Empty clauses."
         t:ts' -> do
           catchError (mapM_ (unify t) ts') $ \e ->
             throwError $ "Clauses do not all return the same type:\n"
                       ++ unlines (map show ts) ++ "\n"
                       ++ "Unification failed with error: " ++ e
           subs <- substitution
           return (instantiateMetas subs t)



-- Type Checking

checkify :: Term -> Type -> TypeChecker ()
checkify m (Forall sc)
  = do i <- newName
       extendTyVarContext [i]
         $ checkify m (instantiate sc [TyVar (TyGenerated i)])
checkify (Var x) t
  = do t' <- inferify (Var x)
       equivQuantifiers t' t
checkify (Lam sc) (Fun arg ret)
  = do i <- newName
       extendContext [(i,arg)]
         $ checkify (instantiate sc [Var (Generated i)]) ret
checkify (Lam sc) t
  = throwError $ "Cannot check term: " ++ show (Lam sc) ++ "\n"
              ++ "Against non-function type: " ++ show t
checkify m t
  = do t' <- inferify m
       catchError (unify t t') $ \e ->
         throwError $ "Expected term: " ++ show m ++ "\n"
                   ++ "To have type: " ++ show t ++ "\n"
                   ++ "Instead found type: " ++ show t' ++ "\n"
                   ++ "Unification failed with error: " ++ e

equivQuantifiers :: Type -> Type -> TypeChecker ()
equivQuantifiers t (Forall sc')
  = do i <- newName
       equivQuantifiers t (instantiate sc' [TyVar (TyGenerated i)])
equivQuantifiers (Forall sc) t'
  = do meta <- newMetaVar
       let x2 = Meta meta
       equivQuantifiers (instantiate sc [x2]) t'
equivQuantifiers (Fun arg ret) (Fun arg' ret')
  = do --unify arg arg'
       equivQuantifiers arg' arg
       equivQuantifiers ret ret'
equivQuantifiers t t'
  = unify t t'

checkifyPattern :: Pattern -> Type -> TypeChecker Context
checkifyPattern (VarPat _) t
  = do i <- newName
       return [(i,t)]
checkifyPattern (ConPat c ps) t
  = do ConSig n sc <- typeInSignature c
       (args',ret') <- instantiateParams n sc
       let lps = length ps
           largs' = length args'
       unless (lps == largs')
         $ throwError $ c ++ " expects " ++ show largs' ++ " "
                   ++ (if largs' == 1 then "arg" else "args")
                   ++ " but was given " ++ show lps
       unify t ret'
       subs <- substitution
       let args'' = map (instantiateMetas subs) args'
       rss <- zipWithM checkifyPattern ps args''
       return $ concat rss



-- type checking succees exactly when checkification succeeds
-- and there is a substitution for every meta-variable

metasSolved :: TypeChecker ()
metasSolved = do s <- get
                 unless (tcNextMeta s == length (tcSubs s))
                   $ throwError "Not all metavariables have been solved."

check :: Term -> Type -> TypeChecker ()
check m t = do checkify m t
               metasSolved
                
infer :: Term -> TypeChecker Type
infer m = do t <- inferify m
             metasSolved
             subs <- substitution
             return $ instantiateMetas subs t