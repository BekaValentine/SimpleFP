{-# OPTIONS -Wall #-}
{-# LANGUAGE TypeFamilies #-}

module Simple.Unification.TypeChecking where

import Control.Monad.Except
import Control.Monad.State
import Data.List (intercalate,nubBy,find)

import Scope
import TypeChecker
import Simple.Core.Term
import Simple.Core.Type



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

type Context = [(Int,String,Type)]




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
  = runStateT checker (TCState sig defs ctx i 0 [])

occurs :: MetaVar -> Type -> Bool
occurs _ (TyCon _) = False
occurs x (Fun a b) = occurs x a || occurs x b
occurs x (Meta y)  = x == y


solve :: [Equation] -> TypeChecker Substitution
solve eqs0 = go eqs0 []
  where
    go :: [Equation] -> Substitution -> TypeChecker Substitution
    go [] subs' = return subs'
    go (Equation (Meta x) (Meta y) : eqs) subs'
      | x == y
        = go eqs subs'
      | otherwise
        = go eqs ((x,Meta y):subs')
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
    go (Equation (TyCon tycon1) (TyCon tycon2) : eqs) subs'
      = do unless (tycon1 == tycon2)
             $ throwError $ "Mismatching type constructors " ++ tycon1 ++ " and " ++ tycon2
           go eqs subs'
    go (Equation (Fun a1 b1) (Fun a2 b2) : eqs) subs'
      = go (Equation a1 a2 : Equation b1 b2 : eqs) subs'
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
               subs2' = nubBy (\(a,_) (b,_) -> a == b) (map (\(k,v) -> (k,instantiateMetas subs2 v)) subs2)
           putSubstitution subs2'
    
    substituteContext
      = do ctx <- context
           subs2 <- substitution
           putContext (map (\(i,x,t) -> (i,x,instantiateMetas subs2 t)) ctx)


unify :: Type -> Type -> TypeChecker ()
unify p q
  = do subs' <-  solve [Equation p q]
       addSubstitutions subs'

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
typeInDefinitions n
  = do defs <- definitions
       case find (\(n',_,_) -> n' == n) defs of
         Nothing      -> throwError $ "Unknown constant/defined term: " ++ n
         Just (_,_,t) -> return t

typeInContext :: Int -> TypeChecker Type
typeInContext i
  = do ctx <- context
       case find (\(j,_,_) -> j == i) ctx of
         Nothing      -> throwError "Unbound automatically generated variable."
         Just (_,_,t) -> return t

typeInSignature :: String -> TypeChecker ConSig
typeInSignature n
  = do Signature _ consigs <- signature
       case lookup n consigs of
         Nothing -> throwError $ "Unknown constructor: " ++ n
         Just t  -> return t

tyconExists :: String -> TypeChecker ()
tyconExists n
  = do Signature tycons _ <- signature
       unless (n `elem` tycons)
         $ throwError $ "Unknown type constructor: " ++ n



-- Type well-formedness

isType :: Type -> TypeChecker ()
isType (TyCon tc) = tyconExists tc
isType (Fun a b)  = isType a >> isType b
isType (Meta _)   = return ()



-- Type Inference

inferify :: Term -> TypeChecker Type
inferify (Var (Name x))
  = typeInDefinitions x
inferify (Var (Generated _ i))
  = typeInContext i
inferify (Ann m t)
  = do checkify m t
       return t
inferify (Lam sc)
  = do i <- newName
       meta <- newMetaVar
       let arg = Meta meta
       ret <- extendContext [(i, head (names sc), arg)]
                $ inferify (instantiate sc [Var (Generated (head (names sc)) i)])
       subs <- substitution
       return $ Fun (instantiateMetas subs arg) ret
inferify (App f a)
  = do Fun arg ret <- inferify f
       checkify a arg
       return ret
inferify (Con c as)
  = do ConSig args ret <- typeInSignature c
       let las = length as
           largs = length args
       unless (las == largs)
         $ throwError $ c ++ " expects " ++ show largs ++ " "
                   ++ (if largs == 1 then "arg" else "args")
                   ++ " but was given " ++ show las
       checkifyMulti as args
       return ret
  where
    checkifyMulti :: [Term] -> [Type] -> TypeChecker ()
    checkifyMulti []     []     = return ()
    checkifyMulti (m:ms) (t:ts) = do subs <- substitution
                                     checkify m (instantiateMetas subs t)
                                     checkifyMulti ms ts
    checkifyMulti _      _      = throwError "Mismatched constructor signature lengths."
inferify (Case ms cs)
  = do ts <- mapM inferify ms
       inferifyClauses ts cs

inferifyClause :: [Type] -> Clause -> TypeChecker Type
inferifyClause patTys (Clause psc sc)
  = do let lps = length (descope Name psc)
       unless (length patTys == lps)
         $ throwError $ "Mismatching number of patterns. Expected " ++ show (length patTys)
                     ++ " but found " ++ show (lps)
       ctx' <- forM (names psc) $ \x -> do
                 i <- newName
                 m <- newMetaVar
                 return (i, x, Meta m)
       let is = [ i | (i,_,_) <- ctx' ]
           xs1 = zipWith Generated (names psc) is
           xs2 = map Var (removeByDummies (names psc) xs1)
       extendContext ctx' $ do
         zipWithM_ checkifyPattern (instantiate psc xs1) patTys
         inferify (instantiate sc xs2)


inferifyClauses :: [Type] -> [Clause] -> TypeChecker Type
inferifyClauses patTys cs
  = do ts <- mapM (inferifyClause patTys) cs
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
checkify (Lam sc) (Fun arg ret)
  = do i <- newName
       extendContext [(i, head (names sc), arg)]
         $ checkify (instantiate sc [Var (Generated (head (names sc)) i)]) ret
checkify (Lam sc) t
  = throwError $ "Cannot check term: " ++ show (Lam sc) ++ "\n"
              ++ "Against non-function type: " ++ show t
checkify m t
  = do t' <- infer m
       catchError (unify t t') $ \e ->
         throwError $ "Expected term: " ++ show m ++ "\n"
                   ++ "To have type: " ++ show t ++ "\n"
                   ++ "Instead found type: " ++ show t' ++ "\n"
                   ++ "Unification failed with error: " ++ e

checkifyPattern :: Pattern -> Type -> TypeChecker ()
checkifyPattern (VarPat (Name _)) _
  = return ()
checkifyPattern (VarPat (Generated _ i)) t
  = do t' <- typeInContext i
       unify t t'
checkifyPattern (ConPat c ps) t
  = do ConSig args ret <- typeInSignature c
       let lps = length ps
           largs = length args
       unless (lps == largs)
         $ throwError $ c ++ " expects " ++ show largs ++ " "
                   ++ (if largs == 1 then "arg" else "args")
                   ++ " but was given " ++ show lps
       unify t ret
       subs <- substitution
       zipWithM_ checkifyPattern ps (map (instantiateMetas subs) args)



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