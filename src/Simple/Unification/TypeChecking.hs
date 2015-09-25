module Simple.Unification.TypeChecking where

import System.IO.Unsafe

import Control.Applicative ((<$>))
import Control.Monad (guard,forM,zipWithM)
import Control.Monad.State
import Data.List (intercalate,nubBy,find)
import Data.Maybe (fromMaybe,fromJust)

import Env
import Scope
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



-- Definitions

type Definitions = [(String,Term,Type)]


-- Contexts

type Context = [(Int,Type)]




-- Unifying Type Checkers

data Equation = Equation Type Type

type MetaVar = Int

type Substitution = [(MetaVar,Type)]

data TCState
  = TCState
    { tcSig :: Signature
    , tcDefs :: Definitions
    , tcCtx :: Context
    , tcNextName :: Int
    , tcNextMeta :: MetaVar
    , tcSubs :: Substitution
    }

type TypeChecker a = StateT TCState Maybe a

runTypeChecker :: TypeChecker a -> Signature -> Definitions -> Context -> Maybe a
runTypeChecker checker sig defs ctx
  = fmap fst (runStateT checker (TCState sig defs ctx 0 0 []))
      

failure :: TypeChecker a
failure = StateT (\_ -> Nothing)

signature :: TypeChecker Signature
signature = tcSig <$> get

definitions :: TypeChecker Definitions
definitions = tcDefs <$> get

putDefinitions :: Definitions -> TypeChecker ()
putDefinitions defs = do s <- get
                         put (s { tcDefs = defs })

context :: TypeChecker Context
context = tcCtx <$> get

putContext :: Context -> TypeChecker ()
putContext ctx = do s <- get
                    put (s { tcCtx = ctx })

extendDefinitions :: Definitions -> TypeChecker a -> TypeChecker a
extendDefinitions edefs tc
  = do defs <- definitions
       putDefinitions (edefs++defs)
       x <- tc
       putDefinitions defs
       return x

extendContext :: Context -> TypeChecker a -> TypeChecker a
extendContext ectx tc
  = do ctx <- context
       putContext (ectx++ctx)
       x <- tc
       putContext ctx
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
occurs x (TyCon _) = False
occurs x (Fun a b) = occurs x a || occurs x b
occurs x (Meta y)  = x == y


solve :: [Equation] -> Maybe Substitution
solve eqs = go eqs []
  where
    go [] subs' = return subs'
    go (Equation (Meta x) t2 : eqs) subs'
      = do guard (not (occurs x t2))
           go eqs ((x,t2):subs')
    go (Equation t1 (Meta y) : eqs) subs'
      = do guard (not (occurs y t1))
           go eqs ((y,t1):subs')
    go (Equation (TyCon tycon1) (TyCon tycon2) : eqs) subs'
      = do guard (tycon1 == tycon2)
           go eqs subs'
    go (Equation (Fun a1 b1) (Fun a2 b2) : eqs) subs'
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
               subs2' = nubBy (\(a,_) (b,_) -> a == b) (map (\(k,v) -> (k,instantiateMetas subs2 v)) subs2)
           putSubstitution subs2'
    
    substituteContext
      = do ctx <- context
           subs2 <- substitution
           putContext (map (\(x,t) -> (x,instantiateMetas subs2 t)) ctx)


unify :: Type -> Type -> TypeChecker ()
unify p q = case solve [Equation p q] of
              Nothing    -> failure
              Just subs' -> addSubstitutions subs'

instantiateMetas :: Substitution -> Type -> Type
instantiateMetas _ (TyCon tycon)
  = TyCon tycon
instantiateMetas subs (Fun a b)
  = Fun (instantiateMetas subs a) (instantiateMetas subs b)
instantiateMetas subs (Meta i)
  = case lookup i subs of
      Nothing -> Meta i
      Just t  -> instantiateMetas subs t



typeInDefinitions :: String -> TypeChecker Type
typeInDefinitions n = do defs <- definitions
                         case find (\(n',_,_) -> n' == n) defs of
                           Nothing      -> failure
                           Just (_,_,t) -> return t

typeInContext :: Int -> TypeChecker Type
typeInContext i = do ctx <- context
                     case lookup i ctx of
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

inferify :: Term -> TypeChecker Type
inferify (Var (Name x))
  = typeInDefinitions x
inferify (Var (Generated i))
  = typeInContext i
inferify (Ann m t)
  = do checkify m t
       return t
inferify (Lam sc)
  = do i <- newName
       arg <- newMetaVar
       ret <- extendContext [(i,arg)]
                $ inferify (instantiate sc [Var (Generated i)])
       subs <- substitution
       return $ Fun (instantiateMetas subs arg) ret
inferify (App f a)
  = do Fun arg ret <- inferify f
       checkify a arg
       return ret
inferify (Con c as)
  = do ConSig args ret <- typeInSignature c
       guard $ length as == length args
       checkifyMulti as args
       return ret
  where
    checkifyMulti :: [Term] -> [Type] -> TypeChecker ()
    checkifyMulti []     []     = return ()
    checkifyMulti (m:ms) (t:ts) = do subs <- substitution
                                     checkify m (instantiateMetas subs t)
                                     checkifyMulti ms ts
    checkifyMulti _      _      = failure
inferify (Case m cs)
  = do t <- inferify m
       inferifyClauses t cs

inferifyClause :: Type -> Clause -> TypeChecker Type
inferifyClause patTy (Clause p sc)
  = do ctx' <- checkifyPattern p patTy
       let xs = [ Var (Generated i) | (i,_) <- ctx' ]
       ctx <- context
       extendContext ctx'
         $ inferify (instantiate sc xs)


inferifyClauses :: Type -> [Clause] -> TypeChecker Type
inferifyClauses patTy cs
  = do ts <- sequence $ map (inferifyClause patTy) cs
       case ts of
         t:ts -> do
           sequence_ (map (unify t) ts)
           subs <- substitution
           return (instantiateMetas subs t)
         _ -> failure



-- Type Checking

checkify :: Term -> Type -> TypeChecker ()
checkify (Var x) t
  = do t' <- inferify (Var x)
       unify t t'
checkify (Ann m t') t
  = do unify t t'
       subs <- substitution
       checkify m (instantiateMetas subs t')
checkify (Lam sc) (Fun arg ret)
  = do i <- newName
       extendContext [(i,arg)]
         $ checkify (instantiate sc [Var (Generated i)]) ret
checkify (App f a) t
  = do t' <- inferify (App f a)
       unify t t'
checkify (Con c as) t
  = do t' <- inferify (Con c as)
       unify t t'
checkify (Case m cs) t
  = do t' <- inferify (Case m cs)
       unify t t'
checkify _ _
  = failure

checkifyPattern :: Pattern -> Type -> TypeChecker Context
checkifyPattern VarPat t
  = do i <- newName
       return [(i,t)]
checkifyPattern (ConPat c ps) t
  = do ConSig args ret <- typeInSignature c
       guard $ length ps == length args
       unify t ret
       subs <- substitution
       rss <- zipWithM checkifyPattern ps (map (instantiateMetas subs) args)
       return $ concat rss



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