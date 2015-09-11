{-# LANGUAGE RecursiveDo #-}
{-# OPTIONS -Wall #-}

module Poly.Constraint.TypeChecking where

import Control.Applicative ((<$>))
import Control.Monad (guard,forM,zipWithM,replicateM)
import Control.Monad.Trans.State
import Data.List (intercalate,nubBy,find)
import Data.Maybe (fromMaybe)

import Scope
import Poly.Core.Term
import Poly.Core.Type




freshen :: [String] -> String -> String
freshen xs x
  | x `elem` xs = freshen xs (x ++ "'")
  | otherwise   = x


-- Signatures

-- params, arg types, return type
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

type TypeChecker a = StateT TCState Maybe a

runTypeChecker :: TypeChecker a -> Signature -> Definitions -> Context -> Maybe a
runTypeChecker checker sig defs ctx
  = fmap fst (runStateT checker (TCState sig defs ctx [] 0 0 []))
      

failure :: TypeChecker a
failure = StateT (\_ -> Nothing)

signature :: TypeChecker Signature
signature = tcSig <$> get

definitions :: TypeChecker Definitions
definitions = tcDefs <$> get

context :: TypeChecker Context
context = tcCtx <$> get

tyVarContext :: TypeChecker TyVarContext
tyVarContext = tcTyVarCtx <$> get

putDefinitions :: Definitions -> TypeChecker ()
putDefinitions defs = do s <- get
                         put (s { tcDefs = defs })

putContext :: Context -> TypeChecker ()
putContext ctx = do s <- get
                    put (s { tcCtx = ctx })

putTyVarContext :: TyVarContext -> TypeChecker ()
putTyVarContext tyVarCtx = do s <- get
                              put (s { tcTyVarCtx = tyVarCtx })

extendDefinitions :: Definitions -> TypeChecker a -> TypeChecker a
extendDefinitions edefs tc
  = do defs <- definitions
       putDefinitions (edefs ++ defs)
       x <- tc
       putDefinitions defs
       return x

extendContext :: Context -> TypeChecker a -> TypeChecker a
extendContext ectx tc = do ctx <- context
                           putContext (ectx++ctx)
                           x <- tc
                           putContext ctx
                           return x

extendTyVarContext :: TyVarContext -> TypeChecker a -> TypeChecker a
extendTyVarContext etyVarCtx tc = do tyVarCtx <- tyVarContext
                                     putTyVarContext (etyVarCtx ++ tyVarCtx)
                                     x <- tc
                                     putTyVarContext tyVarCtx
                                     return x

newName :: TypeChecker Int
newName = do s <- get
             put (s { tcNextName = 1 + tcNextName s })
             return $ tcNextName s

newMetaVar :: TypeChecker Type
newMetaVar = do s <- get
                put (s { tcNextMeta = 1 + tcNextMeta s })
                return $ Meta (tcNextMeta s)

substitution :: TypeChecker Substitution
substitution = tcSubs <$> get

putSubstitution :: Substitution -> TypeChecker ()
putSubstitution subs = do s <- get
                          put (s { tcSubs = subs })

occurs :: MetaVar -> Type -> Bool
occurs x (TyCon _ args) = any (occurs x) args
occurs x (Fun a b)      = occurs x a || occurs x b
occurs x (Meta y)       = x == y
occurs _ (TyVar _)      = False
occurs x (Forall sc)    = occurs x (instantiate sc (repeat (TyVar undefined)))


solve :: [Equation] -> TypeChecker Substitution
solve eqs0 = go eqs0 []
  where
    go [] subs' = return subs'
    go (Equation (Meta x) t2 : eqs) subs'
      = do guard (not (occurs x t2))
           go eqs ((x,t2):subs')
    go (Equation t1 (Meta y) : eqs) subs'
      = do guard (not (occurs y t1))
           go eqs ((y,t1):subs')
    go (Equation (TyCon tycon1 args1) (TyCon tycon2 args2) : eqs) subs'
      = do guard $ tycon1 == tycon2 && length args1 == length args2
           go (zipWith Equation args1 args2 ++ eqs) subs'
    go (Equation (Fun a1 b1) (Fun a2 b2) : eqs) subs'
      = go (Equation a1 a2 : Equation b1 b2 : eqs) subs'
    go (Equation (TyVar x) (TyVar y) : eqs) subs'
      = do guard (x == y)
           go eqs subs'
    go (Equation (Forall sc) (Forall sc') : eqs) subs'
      = do i <- newName
           let b = instantiate sc [TyVar (TyGenerated i)]
               b' = instantiate sc' [TyVar (TyGenerated i)]
           go (Equation b b' : eqs) subs'
    go _ _ = failure


addSubstitutions :: Substitution -> TypeChecker ()
addSubstitutions subs0
  = do completeSubstitution subs0
       substituteContext
  where
    
    completeSubstitution subs'
      = do subs <- substitution
           let subs2 = subs' ++ subs
               subs2' = nubBy (\(a,_) (b,_) -> a == b) (map (\(k,v) -> (k, substitute subs2 v)) subs2)
           putSubstitution subs2'
    
    substitute :: Substitution -> Type -> Type
    substitute s (TyCon tycon args) = TyCon tycon (map (substitute s) args)
    substitute s (Fun a b)          = Fun (substitute s a) (substitute s b)
    substitute s (Meta i)           = case lookup i s of
                                        Nothing -> Meta i
                                        Just t  -> substitute s t
    substitute _ (TyVar x)          = TyVar x
    substitute s (Forall sc)        = Forall (Scope $ \vs -> substitute s (instantiate sc vs))
    
    substituteContext
      = do ctx <- context
           ctx' <- forM ctx $ \(x,t) -> do
                     subs <- substitution
                     return (x,instantiateMetas subs t)
           putContext ctx'


unify :: Type -> Type -> TypeChecker ()
unify p q = do subs' <- solve [Equation p q]
               addSubstitutions subs'

instantiateMetas :: Substitution -> Type -> Type
instantiateMetas subs (TyCon tycon args)
  = TyCon tycon (map (instantiateMetas subs) args)
instantiateMetas subs (Fun a b)
  = Fun (instantiateMetas subs a) (instantiateMetas subs b)
instantiateMetas subs (Meta x)
  = fromMaybe (Meta x) (lookup x subs)
instantiateMetas _ (TyVar x)
  = TyVar x
instantiateMetas subs (Forall sc)
  = Forall (Scope $ \vs -> instantiateMetas subs (instantiate sc vs))


typeInContext :: Int -> TypeChecker Type
typeInContext i = do ctx <- context
                     case lookup i ctx of
                       Nothing -> failure
                       Just t  -> return t

typeInDefinitions :: String -> TypeChecker Type
typeInDefinitions n = do defs <- definitions
                         case find (\(n',_,_) -> n' == n) defs of
                           Nothing      -> failure
                           Just (_,_,t) -> return t

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

isType :: Type -> TypeChecker ()
isType (Meta _)     = return ()
isType (TyCon c as) = do n <- tyconExists c
                         guard $ n == length as
                         sequence_ (map isType as)
isType (Fun a b)    = isType a >> isType b
isType (TyVar _)    = return ()
isType (Forall sc)  = do i <- newName
                         isType (instantiate sc [TyVar (TyGenerated i)])


-- Inserting param variables into con data

instantiateParams :: Int -> Scope Type ([Type],Type) -> TypeChecker ([Type],Type)
instantiateParams n sc
  = do ms <- replicateM n newMetaVar
       return $ instantiate sc ms



-- Instantiating quantified values until there are no more initial quantifiers
instantiateQuantifiers :: Type -> TypeChecker Type
instantiateQuantifiers (Forall sc)
  = do m <- newMetaVar
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
       arg <- newMetaVar
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
       guard $ length as == length args'
       checkifyMulti as args'
       subs <- substitution
       return $ instantiateMetas subs ret'
  where
    checkifyMulti :: [Term] -> [Type] -> TypeChecker ()
    checkifyMulti []     []     = return ()
    checkifyMulti (m:ms) (t:ts) = do subs <- substitution
                                     checkify m (instantiateMetas subs t)
                                     checkifyMulti ms ts
    checkifyMulti _      _      = failure
inferify (Case m cs) = do t <- inferify m
                          t' <- inferifyClauses t cs
                          return t'

inferifyClause :: Type -> Clause -> TypeChecker Type
inferifyClause patTy (Clause p sc)
  = do ctx' <- checkifyPattern p patTy
       let xs = [ Var (Generated i) | (i,_) <- ctx' ]
       b' <- extendContext ctx'
               $ inferify (instantiate sc xs)
       return b'


inferifyClauses :: Type -> [Clause] -> TypeChecker Type
inferifyClauses patTy cs = do ts <- sequence $ map (inferifyClause patTy) cs
                              case ts of
                                t:ts' -> do
                                  sequence_ (map (unify t) ts')
                                  subs <- substitution
                                  return $ instantiateMetas subs t
                                _ -> failure



-- Type Checking

checkify :: Term -> Type -> TypeChecker ()
checkify m (Forall sc)
  = do i <- newName
       let b' = instantiate sc [TyVar (TyGenerated i)]
       m' <- extendTyVarContext [i]
               $ checkify m b'
       return m'
checkify (Var x) t
  = do t' <- inferify (Var x)
       equivQuantifiers t' t
checkify (Ann m t') t
  = do isType t'
       unify t t'
       subs <- substitution
       checkify m (instantiateMetas subs t')
checkify (Lam sc) t
  = do i <- newName
       arg <- newMetaVar
       ret <- newMetaVar
       unify t (Fun arg ret)
       subs <- substitution
       extendContext [(i,instantiateMetas subs arg)]
         $ checkify (instantiate sc [Var (Generated i)]) (instantiateMetas subs ret)
checkify (App f a) t
  = do arg <- newMetaVar
       checkify f (Fun arg t)
       subs <- substitution
       checkify a (instantiateMetas subs arg)
checkify (Con c as) t
  = do t' <- inferify (Con c as)
       unify t t'
checkify (Case m cs) t
  = do t' <- inferify m
       checkifyClauses t' cs t

equivQuantifiers :: Type -> Type -> TypeChecker ()
equivQuantifiers t (Forall sc')
  = do i <- newName
       equivQuantifiers t (instantiate sc' [TyVar (TyGenerated i)])
equivQuantifiers (Forall sc) t'
  = do x2 <- newMetaVar
       equivQuantifiers (instantiate sc [x2]) t'
equivQuantifiers (Fun arg ret) (Fun arg' ret')
  = do --unify arg arg'
       equivQuantifiers arg' arg
       equivQuantifiers ret ret'
equivQuantifiers t t'
  = unify t t'

checkifyPattern :: Pattern -> Type -> TypeChecker Context
checkifyPattern VarPat t
  = do i <- newName
       return [(i,t)]
checkifyPattern (ConPat c ps) t
  = do ConSig n sc <- typeInSignature c
       (args',ret') <- instantiateParams n sc
       guard $ length ps == length args'
       unify t ret'
       subs <- substitution
       let args'' = map (instantiateMetas subs) args'
       rss <- zipWithM checkifyPattern ps args''
       return $ concat rss

checkifyClauses :: Type -> [Clause] -> Type -> TypeChecker ()
checkifyClauses _ [] _ = return ()
checkifyClauses patTy (Clause p sc:cs) t
  = do ctx' <- checkifyPattern p patTy
       let xs = [ Var (Generated i) | (i,_) <- ctx' ]
       extendContext ctx'
         $ checkify (instantiate sc xs) t
       subs <- substitution
       checkifyClauses
         (instantiateMetas subs patTy)
         cs
         (instantiateMetas subs t)



-- type checking succees exactly when checkification succeeds
-- and there is a substitution for every meta-variable

metasSolved :: TypeChecker ()
metasSolved = do s <- get
                 guard $ tcNextMeta s == length (tcSubs s)

check :: Term -> Type -> TypeChecker ()
check m t = do checkify m t
               metasSolved
                
infer :: Term -> TypeChecker Type
infer m = do t <- inferify m
             metasSolved
             subs <- substitution
             return $ instantiateMetas subs t