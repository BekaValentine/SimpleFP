{-# OPTIONS -Wall #-}
{-# LANGUAGE TypeFamilies #-}

module Modular.Unification.TypeChecking where

import Control.Applicative ((<$>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List (nubBy,find,nub)

import Abs
import Eval
import Plicity
import Scope
import TypeChecker
import Modular.Core.Abstraction ()
import Modular.Core.ConSig
import Modular.Core.Evaluation ()
import Modular.Core.Term





-- Definitions

type Definitions = [((String,String),Term,Term)]




-- Contexts

type Context = [(Int,String,Term)]




-- Unifying Type Checkers

data Equation = Equation Term Term

type MetaVar = Int

type Substitution = [(MetaVar,Term)]

type ModuleAliases = [(Either String (String,String), (String,String))]

data TCState
  = TCState
    { tcSig :: Signature Term
    , tcDefs :: Definitions
    , tcCtx :: Context
    , tcNextName :: Int
    , tcNextMeta :: MetaVar
    , tcSubs :: Substitution
    , tcAliases :: ModuleAliases
    , tcModuleNames :: [String]
    }

instance TypeCheckerState TCState where
  type Sig TCState = Signature Term
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

runTypeChecker :: TypeChecker a -> Signature Term -> Definitions -> Context -> Int -> ModuleAliases -> [String] -> Either String (a,TCState)
runTypeChecker checker sig defs ctx i als mods
  = runStateT checker (TCState sig defs ctx i 0 [] als mods)

aliases :: TypeChecker ModuleAliases
aliases = fmap tcAliases get

putAliases :: ModuleAliases -> TypeChecker ()
putAliases als = do s <- get
                    put s { tcAliases = als }

moduleNames :: TypeChecker [String]
moduleNames = fmap tcModuleNames get

occurs :: MetaVar -> Term -> Bool
occurs x (Meta y)         = x == y
occurs _ (Var _)          = False
occurs _ (DottedVar _ _)  = False
occurs x (Ann m t)        = occurs x m || occurs x t
occurs _ Type             = False
occurs x (Fun _ a sc)     = occurs x a || occurs x (descope (Var . Name) sc)
occurs x (Lam _ sc)       = occurs x (descope (Var . Name) sc)
occurs x (App _ f a)      = occurs x f || occurs x a
occurs x (Con _ as)       = any (occurs x . snd) as
occurs x (Case as mot cs) = any (occurs x) as || occursCaseMotive mot || any occursClause cs
  where
    occursCaseMotive (CaseMotiveNil m) = occurs x m
    occursCaseMotive (CaseMotiveCons a sc)
      = occurs x a || occursCaseMotive (descope (Var . Name) sc)
    
    occursClause (Clause psc sc) = any occursPattern (descope Name psc) || occurs x (descope (Var . Name) sc)
    
    occursPattern (VarPat _) = False
    occursPattern (ConPat _ xs) = any (occursPattern . snd) xs
    occursPattern (AssertionPat m) = occurs x m
    occursPattern MakeMeta = False

solve :: [Equation] -> TypeChecker Substitution
solve eqs0 = go eqs0 []
  where
    evalWithSubs :: Substitution -> Equation -> TypeChecker Equation
    evalWithSubs subs (Equation l r)
      = do l' <- evaluate (instantiateMetas subs l)
           r' <- evaluate (instantiateMetas subs r)
           return (Equation l' r')
    
    go [] subs' = return subs'
    go (Equation (Meta x) (Meta y) : eqs) subs'
      | x == y
        = go eqs subs'
      | otherwise
        = do eqs' <- mapM (evalWithSubs ((x,Meta y):subs')) eqs
             go eqs' ((x,Meta y):subs')
    go (Equation (Meta x) t2 : eqs) subs'
      = do unless (not (occurs x t2))
             $ throwError $ "Cannot unify because " ++ show (Meta x)
                         ++ " occurs in " ++ show t2
           eqs' <- mapM (evalWithSubs ((x,t2):subs')) eqs
           go eqs' ((x,t2):subs')
    go (Equation t1 (Meta y) : eqs) subs'
      = do unless (not (occurs y t1))
             $ throwError $ "Cannot unify because " ++ show (Meta y)
                         ++ " occurs in " ++ show t1
           eqs' <- mapM (evalWithSubs ((y,t1):subs')) eqs
           go eqs' ((y,t1):subs')
    go (Equation (Var x) (Var y) : eqs) subs'
      = do unless (x == y)
             $ throwError $ "Cannot unify variables " ++ show (Var x)
            ++ " and " ++ show (Var y)
           go eqs subs'
    go (Equation (DottedVar m1 x1) (DottedVar m2 x2):eqs) subs'
      = do unless (m1 == m2 && x1 == x2)
             $ throwError $ "Cannot unify symbols " ++ show (DottedVar m1 x1)
            ++ " and " ++ show (DottedVar m2 x2)
           go eqs subs'
    go (Equation (Ann m1 t1) (Ann m2 t2) : eqs) subs'
      = go (Equation m1 m2 : Equation t1 t2 : eqs) subs'
    go (Equation Type Type : eqs) subs'
      = go eqs subs'
    go (Equation (Fun plic1 a1 sc1) (Fun plic2 a2 sc2) : eqs) subs'
      = do unless (plic1 == plic2)
             $ throwError $ "Mismatched plicities when trying to unify "
                         ++ show (Fun plic1 a1 sc1) ++ " with "
                         ++ show (Fun plic2 a2 sc2)
           i <- newName
           let b1 = instantiate sc1 [Var (Generated (head (names sc1)) i)]
               b2 = instantiate sc2 [Var (Generated (head (names sc2)) i)]
           go (Equation a1 a2 : Equation b1 b2 : eqs) subs'
    go (Equation (Lam plic1 sc1) (Lam plic2 sc2) : eqs) subs'
      = do unless (plic1 == plic2)
             $ throwError $ "Mismatched plicities when trying to unify "
                         ++ show (Lam plic1 sc1) ++ " with "
                         ++ show (Lam plic2 sc2)
           i <- newName
           let b1 = instantiate sc1 [Var (Generated (head (names sc1)) i)]
               b2 = instantiate sc2 [Var (Generated (head (names sc2)) i)]
           go (Equation b1 b2 : eqs) subs'
    go (Equation (App plic1 f1 a1) (App plic2 f2 a2) : eqs) subs'
      = do unless (plic1 == plic2)
             $ throwError $ "Mismatched plicities when trying to unify "
                         ++ show (App plic1 f1 a1) ++ " with "
                         ++ show (App plic2 f2 a2)
           go (Equation f1 f2 : Equation a1 a2 : eqs) subs'
    go (Equation (Con c1 as1) (Con c2 as2) : eqs) subs'
      = do unless (c1 == c2)
             $ throwError $ "Mismatching constructors " ++ show c1 ++ " and " ++ show c2
           unless (length as1 == length as2)
             $ throwError $ "Mismatching number of arguments in "
                         ++ show (Con c1 as1) ++ " and "
                         ++ show (Con c2 as2)
           eqs' <- zipConArgs as1 as2
           go (eqs' ++ eqs) subs'
      where
        zipConArgs :: [(Plicity,Term)] -> [(Plicity,Term)] -> TypeChecker [Equation]
        zipConArgs [] [] = return []
        zipConArgs ((plic1',a1'):as1') ((plic2',a2'):as2')
          = if plic1' == plic2'
            then do
              eqs' <- zipConArgs as1' as2'
              return (Equation a1' a2':eqs')
            else
              throwError "Mismatching plicity."
        zipConArgs _ _
          = throwError "Mismatching number of arguments."
    go (Equation (Case as1 mot1 cs1) (Case as2 mot2 cs2) : eqs) subs'
      = do unless(length as1 == length as2)
             $ throwError $ "Mismatching number of case arguments in "
                         ++ show (Case as1 mot1 cs1) ++ " and "
                         ++ show (Case as2 mot2 cs2)
           unless (length cs1 == length cs2)
             $ throwError $ "Mismatching number of clauses in "
                         ++ show (Case as1 mot1 cs1) ++ " and "
                         ++ show (Case as2 mot2 cs2)
           let argEqs = zipWith Equation as1 as2
           motEqs <- goCaseMotive mot1 mot2
           clauseEqs <- goClauses cs1 cs2
           go (argEqs ++ motEqs ++ clauseEqs ++ eqs) subs'
    go (Equation m m':_) _ = throwError $ "Terms not equal: " ++ show m ++ " and " ++ show m'
    
    goCaseMotive :: CaseMotive -> CaseMotive -> TypeChecker [Equation]
    goCaseMotive (CaseMotiveNil a1) (CaseMotiveNil a2)
      = return [Equation a1 a2]
    goCaseMotive (CaseMotiveCons a1 sc1) (CaseMotiveCons a2 sc2)
      = do i <- newName
           reqs <- goCaseMotive (instantiate sc1 [Var (Generated (head (names sc1)) i)])
                                (instantiate sc2 [Var (Generated (head (names sc2)) i)])
           return (Equation a1 a2 : reqs)
    goCaseMotive mot mot'
      = throwError $ "Motives not equal: " ++ show mot ++ " and " ++ show mot'
    
    goClauses :: [Clause] -> [Clause] -> TypeChecker [Equation]
    goClauses [] [] = return []
    goClauses (Clause psc1 sc1:cs1) (Clause psc2 sc2:cs2)
      = do unless (length (names psc1) == length (names psc2))
             $ throwError "Patterns bind different numbers of arguments."
           is <- replicateM (length (names psc1)) newName
           let xs1 = zipWith Generated (names psc1) is
               xs1' = map Var (removeByDummies (names psc1) xs1)
               xs2 = zipWith Generated (names psc2) is
               xs2' = map Var (removeByDummies (names psc2) xs2)
           reqss <- zipWithM goPattern (instantiate psc1 xs1) (instantiate psc2 xs2)
           reqs' <- goClauses cs1 cs2
           return (Equation (instantiate sc1 xs1') (instantiate sc2 xs2') : concat reqss ++ reqs')
    goClauses _ _ = throwError $ "Mismatching number of clauses."
    
    goPattern :: Pattern -> Pattern -> TypeChecker [Equation]
    goPattern (VarPat x) (VarPat x')
      = do unless (x == x')
             $ throwError $ "Variable patters not equal: " ++ show x ++ " and " ++ show x'
           return []
    goPattern (ConPat c ps) (ConPat c' ps')
      | c == c'   = goPatterns ps ps'
      | otherwise = throwError $ "Mismatching constructors " ++ show c ++ " and " ++ show c'
    goPattern _ _ = throwError "Patterns not equal."
    
    goPatterns :: [(Plicity,Pattern)] -> [(Plicity,Pattern)] -> TypeChecker [Equation]
    goPatterns [] []
      = return []
    goPatterns ((plic1,p1):ps1) ((plic2,p2):ps2)
      = do unless (plic1 == plic2)
             $ throwError "Mismatched plicities when trying to unify constructor sequences."
           eqs <- goPattern p1 p2
           eqs' <- goPatterns ps1 ps2
           return $ eqs ++ eqs'
    goPatterns _ _
      = throwError "Patterns not equal."



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
           subs <- substitution
           putContext (map (\(i,x,t) -> (i,x, instantiateMetas subs t)) ctx)



unify :: Term -> Term -> TypeChecker ()
unify p q = do subs' <- solve [Equation p q]
               addSubstitutions subs'



instantiateMetas :: Substitution -> Term -> Term
instantiateMetas _ (Var x)
  = Var x
instantiateMetas subs (Meta i)
  = case lookup i subs of
      Nothing -> Meta i
      Just t  -> instantiateMetas subs t
instantiateMetas _ (DottedVar m x)
  = DottedVar m x
instantiateMetas subs (Ann m t)
  = Ann (instantiateMetas subs m) (instantiateMetas subs t)
instantiateMetas _ Type
  = Type
instantiateMetas subs (Fun plic a sc)
  = Fun plic
        (instantiateMetas subs a)
        (instantiateMetas subs <$> sc)
instantiateMetas subs (Lam plic sc)
  = Lam plic (instantiateMetas subs <$> sc)
instantiateMetas subs (App plic f a)
  = App plic
        (instantiateMetas subs f)
        (instantiateMetas subs a)
instantiateMetas subs (Con c as)
  = Con c (map (\(plic,a) -> (plic, instantiateMetas subs a)) as)
instantiateMetas subs (Case as mot cs)
  = Case (map (instantiateMetas subs) as)
         (instantiateMetasCaseMotive subs mot)
         (map instantiateClause cs)
  where
    instantiateClause (Clause psc sc)
      = Clause (map (instantiateMetasPat subs) <$> psc)
               (instantiateMetas subs <$> sc)

instantiateMetasCaseMotive :: Substitution -> CaseMotive -> CaseMotive
instantiateMetasCaseMotive subs (CaseMotiveNil a)
      = CaseMotiveNil (instantiateMetas subs a)
instantiateMetasCaseMotive subs (CaseMotiveCons a sc)
  = CaseMotiveCons (instantiateMetas subs a)
                   (instantiateMetasCaseMotive subs <$> sc)

instantiateMetasPat :: Substitution -> Pattern -> Pattern
instantiateMetasPat _ (VarPat x)
  = VarPat x
instantiateMetasPat subs (ConPat c ps)
  = ConPat c (map (\(plic,p) -> (plic,instantiateMetasPat subs p)) ps)
instantiateMetasPat subs (AssertionPat m)
  = AssertionPat (instantiateMetas subs m)
instantiateMetasPat _ MakeMeta
  = MakeMeta




unalias :: Either String (String,String) -> TypeChecker (String,String)
unalias (Left n)
  = do als <- aliases
       case lookup (Left n) als of
         Nothing -> throwError $ "The symbol " ++ n ++ " is not an alias for any "
                              ++ "module-declared symbol."
         Just p  -> return p
unalias (Right (m,n))
  = do als <- aliases
       case lookup (Right (m,n)) als of
         Nothing -> throwError $ "The symbol " ++ m ++ "." ++ n ++ " is not an alias for any "
                              ++ "module-declared symbol."
         Just p  -> return p

typeInSignature :: Constructor -> TypeChecker (Constructor, ConSig Term)
typeInSignature (BareCon n0)
  = do consigs <- signature
       (m,n) <- unalias (Left n0)
       case lookup (m,n) consigs of
         Nothing -> throwError $ "Unknown constructor: " ++ show (DottedCon m n)
         Just t  -> return (DottedCon m n, t)
typeInSignature (DottedCon m n)
  = do consigs <- signature
       (m',n') <- unalias (Right (m,n))
       case lookup (m',n') consigs of
         Nothing -> throwError $ "Unknown constructor: " ++ show (DottedCon m' n')
         Just t  -> return (DottedCon m' n', t)

dottedTypeInDefinitions :: String -> String -> TypeChecker ((String,String),Term)
dottedTypeInDefinitions m x
  = do (m',x') <- unalias (Right (m,x))
       defs <- definitions
       case find (\(mx,_,_) -> mx == (m',x')) defs of
         Nothing      -> throwError $ "Unknown constant/defined term: " ++ m' ++ "." ++ x'
         Just (_,_,t) -> return ((m',x'),t)

typeInDefinitions :: String -> TypeChecker ((String,String),Term)
typeInDefinitions x0
  = do (m,x) <- unalias (Left x0)
       defs <- definitions
       case find (\(mx,_,_) -> mx == (m,x)) defs of
         Nothing      -> throwError $ "Unknown constant/defined term: " ++ m ++ "." ++ x
         Just (_,_,t) -> return ((m,x),t)

typeInContext :: Int -> TypeChecker Term
typeInContext i
  = do ctx <- context
       case find (\(j,_,_) -> j == i) ctx of
         Nothing      -> throwError "Unbound automatically generated variable."
         Just (_,_,t) -> return t

evaluate :: Term -> TypeChecker Term
evaluate m
  = do defs <- definitions
       case runReaderT (eval m) [ (x,m') | (x,m',_) <- defs ] of
         Left e   -> throwError e
         Right m' -> return m'



-- Type Inference

inferify :: Term -> TypeChecker (Term,Term)
inferify (Meta i)
  = throwError $ "The metavariable " ++ show (Meta i)
              ++ " appears in checkable code, when it should not."
inferify (Var (Name x0))
  = do ((m,x),t) <- typeInDefinitions x0
       return (DottedVar m x, t)
inferify (Var (Generated x i))
  = do t <- typeInContext i
       return (Var (Generated x i), t)
inferify (DottedVar m x)
  = do ((m',x'),t) <- dottedTypeInDefinitions m x
       return (DottedVar m' x', t)
inferify (Ann m t)
  = do t' <- checkify t Type
       et' <- evaluate t'
       m' <- checkify m et'
       subs <- substitution
       return (instantiateMetas subs m', instantiateMetas subs et')
inferify Type
  = return (Type,Type)
inferify (Fun plic arg sc)
  = do arg' <- checkify arg Type
       i <- newName
       ret' <- extendContext [(i, head (names sc), arg')]
                 $ checkify (instantiate sc [Var (Generated (head (names sc)) i)]) Type
       let sc' :: Scope Term Term
           sc' = Scope (names sc) (abstractOver [i] ret')
       subs <- substitution
       return (instantiateMetas subs (Fun plic arg' sc'), Type)
inferify (Lam _ _)
  = throwError "Cannot infer the type of a lambda expression."
inferify (App plic f a)
  = do (f0,t0) <- inferify f
       et0 <- evaluate t0
       (app',t') <- insertImplicits f0 plic et0
       subs <- substitution
       return (instantiateMetas subs app', instantiateMetas subs t')
  where
    insertImplicits :: Term -> Plicity -> Term -> TypeChecker (Term,Term)
    insertImplicits f' Expl (Fun Expl arg sc)
      = do earg <- evaluate arg
           a' <- checkify a earg
           return (App Expl f' a', instantiate sc [a'])
    insertImplicits f' Impl (Fun Impl arg sc)
      = do earg <- evaluate arg
           a' <- checkify a earg
           return (App Impl f' a', instantiate sc [a'])
    insertImplicits f' Expl (Fun Impl _ sc)
      = do meta <- newMetaVar
           let impla = Meta meta
               newF' = App Impl f' impla
           newT' <- evaluate (instantiate sc [impla])
           insertImplicits newF' Expl newT'
    insertImplicits _ Impl (Fun Expl _ _)
      = throwError $ "Expected an explicit argument but found an implicit argument "
                  ++ "when applying " ++ show f ++ " to " ++ show a ++ " in "
                  ++ "the expression " ++ show (App plic f a)
    insertImplicits _ _ t
      = throwError $ "Cannot insert implicit arguments for non-function type " ++ show t
inferify (Con c as)
  = do (unaliasedC,consig) <- typeInSignature c
       (as',ret) <- inferifyConArgs consig as consig
       subs <- substitution
       return (instantiateMetas subs (Con unaliasedC as'), instantiateMetas subs ret)
  where
    inferifyConArgs _ [] (ConSigNil ret)
      = return ([], ret)
    inferifyConArgs consig ((Expl,m):ms) (ConSigCons Expl arg sc)
      = do subs <- substitution
           earg <- evaluate (instantiateMetas subs arg)
           m' <- checkify m earg
           (ms',ret) <- inferifyConArgs consig ms (instantiate sc [m])
           return ((Expl,m'):ms', ret)
    inferifyConArgs consig ((Impl,m):ms) (ConSigCons Impl arg sc)
      = do subs <- substitution
           earg <- evaluate (instantiateMetas subs arg)
           m' <- checkify m earg
           (ms',ret) <- inferifyConArgs consig ms (instantiate sc [m])
           return ((Impl,m'):ms', ret)
    inferifyConArgs consig ms (ConSigCons Impl _ sc)
      = do meta <- newMetaVar
           let implm = Meta meta
           (ms',ret) <- inferifyConArgs consig ms (instantiate sc [implm])
           return ((Impl,implm):ms', ret)
    inferifyConArgs consig ((Impl,_):_) (ConSigCons Expl _ _)
      = throwError $ "Expected an explicit argument but found an implicit argument "
                  ++ "when checking " ++ show (Con c as)
                  ++ " matches the signature " ++ showConSig (Var . Name) consig
    inferifyConArgs consig _ _
      = do let las = length as
               lsig = conSigLength (Var . Name) consig
           throwError $ show c ++ " expects " ++ show lsig ++ " "
                   ++ (if lsig == 1 then "arg" else "args")
                   ++ " but was given " ++ show las
inferify (Case ms0 mot cs)
  = do mot' <- checkifyCaseMotive mot
       ms0' <- checkifyCaseArgs ms0 mot'
       cs' <- checkifyClauses cs mot'
       ret <- auxMotive ms0' mot'
       subs <- substitution
       return (instantiateMetas subs (Case ms0' mot' cs'), instantiateMetas subs ret)
  where
    checkifyCaseArgs [] (CaseMotiveNil _)
      = return []
    checkifyCaseArgs (m:ms) (CaseMotiveCons a sc)
      = do ea <- evaluate a
           m' <- checkify m ea
           ms' <- checkifyCaseArgs ms (instantiate sc [m])
           return (m':ms')
    checkifyCaseArgs _ _
      = do let lms = length ms0
               lmot = caseMotiveLength mot
           throwError $ "Motive " ++ show mot ++ " expects " ++ show lmot ++ " case "
                   ++ (if lmot == 1 then "arg" else "args")
                   ++ " but was given " ++ show lms
    
    auxMotive [] (CaseMotiveNil a)
      = return a
    auxMotive (m:ms) (CaseMotiveCons _ sc)
      = auxMotive ms (instantiate sc [m])
    auxMotive _ _
      = do let lms = length ms0
               lmot = caseMotiveLength mot
           throwError $ "Motive " ++ show mot ++ " expects " ++ show lmot ++ " case "
                   ++ (if lmot == 1 then "arg" else "args")
                   ++ " but was given " ++ show lms


-- Type Checking
checkify :: Term -> Term -> TypeChecker Term
checkify (Meta i) _
  = throwError $ "The metavariable " ++ show (Meta i)
              ++ " appears in checkable code, when it should not."
checkify (Lam plic sc) t
  = do et <- evaluate t
       case (plic,et) of
         (Expl, Fun Expl arg sc') -> -- \x -> M : (x : A) -> B
           do i <- newName
              eret <- evaluate (instantiate sc' [Var (Generated (head (names sc)) i)])
              m' <- extendContext [(i, head (names sc), arg)]
                      $ checkify
                          (instantiate sc [Var (Generated (head (names sc)) i)])
                          eret
              subs <- substitution
              return (instantiateMetas subs (Lam Expl (Scope (names sc) (abstractOver [i] m'))))
         (Impl, Fun Impl arg sc') -> -- \{y} -> M : {y : A} -> B
           do i <- newName
              eret <- evaluate (instantiate sc' [Var (Generated (head (names sc)) i)])
              m' <- extendContext [(i, head (names sc), arg)]
                      $ checkify
                          (instantiate sc [Var (Generated (head (names sc)) i)])
                          eret
              subs <- substitution
              return (instantiateMetas subs (Lam Impl (Scope (names sc) (abstractOver [i] m'))))
         (Expl, Fun Impl arg sc') -> -- \x -> M : {y : A} -> B
           do i <- newName
              eret <- evaluate (instantiate sc' [Var (Generated (head (names sc)) i)])
              f' <- extendContext [(i, head (names sc), arg)]
                      $ checkify
                          (Lam Expl sc)
                          eret
              subs <- substitution
              return (instantiateMetas subs (Lam Impl (Scope ["_"] (abstractOver ([]::[String]) f'))))
         (Impl, Fun Expl _ _) -> -- \{y} -> M : (x : A) -> B
           throwError $ "Expected an explicit argument but found an implicit argument "
                  ++ "when checking " ++ show (Lam plic sc)
                  ++ " matches the signature " ++ show t
         _ -> throwError $ "Cannot check term: " ++ show (Lam plic sc) ++ "\n"
              ++ "Against non-function type: " ++ show t
checkify (Con c as) t
  = do (unaliasedC,consig) <- typeInSignature c
       (ats, ret) <- dropConArgs as consig
       unify t ret
       as' <- mapM checkifyConArg ats
       subs <- substitution
       return (instantiateMetas subs (Con unaliasedC as'))
  where
    dropConArgs :: [(Plicity,Term)] -> ConSig Term -> TypeChecker ([Either (Plicity,Term) (Plicity,Term,Term)], Term)
    dropConArgs [] (ConSigNil ret)
      = return ([], ret)
    dropConArgs ((Expl,m):ms) (ConSigCons Expl arg sc)
      = do (ats,ret) <- dropConArgs ms (instantiate sc [m])
           return (Right (Expl,m,arg):ats, ret)
    dropConArgs ((Impl,m):ms) (ConSigCons Impl arg sc)
      = do (ats,ret) <- dropConArgs ms (instantiate sc [m])
           return (Right (Impl,m,arg):ats, ret)
    dropConArgs ms (ConSigCons Impl _ sc)
      = do meta <- newMetaVar
           let x = Meta meta
           (ats,ret) <- dropConArgs ms (instantiate sc [x])
           return (Left (Impl,x):ats,ret)
    dropConArgs ((Impl,_):_) (ConSigCons Expl _ _)
      = throwError $ "Mismatching plicits when checking " ++ show (Con c as)
                  ++ " has type " ++ show t
    dropConArgs _ _
      = throwError $ "Mismatching number of arguments when checking " ++ show (Con c as)
                  ++ " has type " ++ show t
    
    checkifyConArg :: Either (Plicity,Term) (Plicity,Term,Term) -> TypeChecker (Plicity,Term)
    checkifyConArg (Left pm)
      = return pm
    checkifyConArg (Right (plic, m, arg))
      = do subs <- substitution
           earg <- evaluate (instantiateMetas subs arg)
           m' <- checkify m earg
           return (plic,m')

checkify m t
  = do (m',t') <- inferify m
       et <- evaluate t
       et' <- evaluate t'
       m'' <- subtype m' et' et
       subs <- substitution
       return (instantiateMetas subs m'')
  where
    subtype :: Term -> Term -> Term -> TypeChecker Term
    subtype m (Fun Expl a sc) (Fun Expl a' sc')
      = do unify a a'
           subs <- substitution
           i <- newName
           let b = instantiateMetas subs (instantiate sc [Var (Generated (head (names sc)) i)])
               b' = instantiateMetas subs (instantiate sc' [Var (Generated (head (names sc)) i)])
           subtype m b b'
    subtype m (Fun Expl a sc) (Fun Impl a' sc')
      = throwError $ "The type " ++ show (Fun Expl a sc) ++ " is not a subtype of " ++ show (Fun Impl a' sc')
    subtype m (Fun Impl a sc) (Fun Expl a' sc')
      = do i <- newMetaVar
           subs <- substitution
           let b = instantiate sc [Meta i]
           subtype (App Impl m (Meta i)) b (Fun Expl a' sc')
    subtype m (Fun Impl a sc) (Fun Impl a' sc')
      = do unify a a'
           i <- newName
           subs <- substitution
           let b = instantiateMetas subs (instantiate sc [Var (Generated (head (names sc)) i)])
               b' = instantiateMetas subs (instantiate sc' [Var (Generated (head (names sc)) i)])
           subtype m b b'
    subtype m t t'
      = do unify t t'
           return m


checkifyCaseMotive :: CaseMotive -> TypeChecker CaseMotive
checkifyCaseMotive (CaseMotiveNil a)
  = do a' <- checkify a Type
       return (CaseMotiveNil a')
checkifyCaseMotive (CaseMotiveCons a sc)
  = do a' <- checkify a Type
       i <- newName
       b' <- extendContext [(i, head (names sc), a')]
               $ checkifyCaseMotive (instantiate sc [Var (Generated (head (names sc)) i)])
       subs <- substitution
       return (instantiateMetasCaseMotive subs (CaseMotiveCons a' (Scope (names sc) (abstractOver [i] b'))))

checkifyPattern :: Pattern -> Term -> TypeChecker (Pattern,Term)
checkifyPattern (VarPat (Name x)) _
  = return (VarPat (Name x), Var (Name x))
checkifyPattern (VarPat (Generated x i)) t
  = do t' <- typeInContext i
       unify t t'
       return (VarPat (Generated x i), Var (Generated x i))
checkifyPattern (ConPat _ _) Type
  = throwError "Cannot pattern match on a type."
checkifyPattern (ConPat c ps0) t
  = do (unaliasedC,sig) <- typeInSignature c
       (ps',xs,ret) <- checkifyPatConArgs sig ps0 sig
       subs <- substitution
       et <- evaluate (instantiateMetas subs t)
       eret <- evaluate (instantiateMetas subs ret)
       unify et eret
       subs' <- substitution
       return ( instantiateMetasPat subs' (ConPat unaliasedC ps')
              , instantiateMetas subs' (Con unaliasedC xs)
              )
  where
    checkifyPatConArgs :: ConSig Term -> [(Plicity,Pattern)] -> ConSig Term -> TypeChecker ([(Plicity,Pattern)],[(Plicity,Term)],Term)
    checkifyPatConArgs _ [] (ConSigNil ret)
      = return ([],[],ret)
    checkifyPatConArgs consig ((Expl,p):ps) (ConSigCons Expl arg sc')
      = do earg <- evaluate arg
           (p',x) <- checkifyPattern p earg
           (ps',xs,ret) <-
             checkifyPatConArgs consig ps (instantiate sc' [x])
           return ( (Expl,p'):ps'
                  , (Expl,x):xs
                  , ret
                  )
    checkifyPatConArgs consig ((Impl,p):ps) (ConSigCons Impl arg sc')
      = do earg <- evaluate arg
           (p',x) <- checkifyPattern p earg
           (ps',xs,ret) <-
             checkifyPatConArgs consig ps (instantiate sc' [x])
           return ( (Impl,p'):ps'
                  , (Impl,x):xs
                  , ret
                  )
    checkifyPatConArgs consig ps (ConSigCons Impl _ sc')
      = do meta <- newMetaVar
           let x = Meta meta
           (ps',xs,ret) <- checkifyPatConArgs
                             consig
                             ps
                             (instantiate sc' [x])
           return ( (Impl,AssertionPat x):ps'
                  , (Impl,x):xs
                  , ret
                  )
    checkifyPatConArgs consig ((Impl,_):_) (ConSigCons Expl _ _)
      = throwError $ "Expected an explicit argument but found an implicit argument "
                  ++ "when checking " ++ show (ConPat c ps0)
                  ++ " matches the signature " ++ showConSig (Var . Name) consig
    checkifyPatConArgs consig _ _
      = do let lps = length ps0
               lsig = conSigLength (Var . Name) consig
           throwError $ show c ++ " expects " ++ show lsig ++ " case "
                   ++ (if lsig == 1 then "arg" else "args")
                   ++ " but was given " ++ show lps
checkifyPattern (AssertionPat m) t
  = do m' <- checkify m t
       subs <- substitution
       let m'' = instantiateMetas subs m'
       return (AssertionPat m'', m'')
checkifyPattern MakeMeta _
  = throwError $ show MakeMeta ++ " should not appear in a checkable pattern."


checkifyClause :: Clause -> CaseMotive -> TypeChecker Clause
checkifyClause (Clause psc sc0) motive
  = do ctx <- forM (names psc) $ \x -> do
                i <- newName
                m <- newMetaVar
                return (i, x, Meta m)
       let is = [ i | (i,_,_) <- ctx ]
           xs1 = zipWith Generated (names psc) is
           xs2 = map Var (removeByDummies (names psc) xs1)
       extendContext ctx $ do
         let ps = instantiate psc xs1
         (ps',ret) <- checkPatternsMotive ps motive
         subs <- substitution
         eret <- evaluate (instantiateMetas subs ret)
         m' <- checkify (instantiate sc0 xs2) eret
         subs' <- substitution
         let ps'' = map (instantiateMetasPat subs') ps'
             psWithMsToBind = [ p | (MakeMeta, AssertionPat p) <- zip ps ps'' ]
             msToBind = nub (psWithMsToBind >>= metas)
         newSubs <- forM msToBind $ \m -> do
                   i <- newName
                   return (m,Var (Generated ("_" ++ show i) i))
         addSubstitutions newSubs
         subs'' <- substitution
         let newPs = bindersByNewMetas ps (map (instantiateMetasPat subs'') ps'')
             newVars = newPs >>= patternVars
             (newNames,newIs) = unzip [ (x,i) | Generated x i <- newVars ]
             newM = instantiateMetas subs'' m'
         return $ Clause (Scope newNames (abstractOver newIs newPs))
                         (Scope (removeByDummies newNames newNames) (abstractOver (removeByDummies newNames newIs) newM))
  where
    bindersByNewMetas :: [Pattern] -> [Pattern] -> [Pattern]
    bindersByNewMetas [] [] = []
    bindersByNewMetas (MakeMeta:guides) (AssertionPat x:ps)
      = termToPattern x : bindersByNewMetas guides ps
    bindersByNewMetas (_:guides) (p:ps)
      = p : bindersByNewMetas guides ps
    
    checkPatternsMotive :: [Pattern] -> CaseMotive -> TypeChecker ([Pattern],Term)
    checkPatternsMotive [] (CaseMotiveNil ret)
      = return ([],ret)
    checkPatternsMotive (MakeMeta:ps) (CaseMotiveCons _ sc')
      = do m <- newMetaVar
           (ps',ret) <-
             checkPatternsMotive ps (instantiate sc' [Meta m])
           return ( AssertionPat (Meta m):ps'
                  , ret
                  )
    checkPatternsMotive (p:ps) (CaseMotiveCons arg sc')
      = do earg <- evaluate arg
           (p',x) <- checkifyPattern p earg
           (ps',ret) <-
             checkPatternsMotive ps (instantiate sc' [x])
           return ( p':ps'
                  , ret
                  )
    checkPatternsMotive _ _
      = do let lps = length (descope Name psc)
               lmot = caseMotiveLength motive
           throwError $ "Motive " ++ show motive ++ " expects " ++ show lmot ++ " case "
                   ++ (if lmot == 1 then "arg" else "args")
                   ++ " but was given " ++ show lps


checkifyClauses :: [Clause] -> CaseMotive -> TypeChecker [Clause]
checkifyClauses [] _
  = return []
checkifyClauses (c:cs) motive
  = do c' <- checkifyClause c motive
       cs' <- checkifyClauses cs motive
       return (c':cs')

checkifyConSig :: ConSig Term -> TypeChecker (ConSig Term)
checkifyConSig (ConSigNil ret)
  = do ret' <- checkify ret Type
       return (ConSigNil ret')
checkifyConSig (ConSigCons plic arg sc)
  = do arg' <- checkify arg Type
       i <- newName
       t <- extendContext [(i, head (names sc), arg')]
              $ checkifyConSig (instantiate sc [Var (Generated (head (names sc)) i)])
       return (ConSigCons plic arg' (Scope (names sc) (abstractOver [i] t)))




-- type checking succees exactly when checkification succeeds
-- and there is a substitution for every meta-variable


metasSolved :: TypeChecker ()
metasSolved = do s <- get
                 unless (tcNextMeta s == length (tcSubs s))
                   $ throwError "Not all metavariables have been solved."

check :: Term -> Term -> TypeChecker Term
check m t = do et <- evaluate t
               m' <- checkify m et
               metasSolved
               subs <- substitution
               return (instantiateMetas subs m')
                
infer :: Term -> TypeChecker (Term,Term)
infer m = do (m',t) <- inferify m
             metasSolved
             subs <- substitution
             et <- evaluate (instantiateMetas subs t)
             return (instantiateMetas subs m', et)