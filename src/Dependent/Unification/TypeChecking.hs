{-# OPTIONS -Wall #-}

module Dependent.Unification.TypeChecking where

import Control.Applicative ((<$>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List (nubBy,find)

import Eval
import Scope
import Dependent.Core.ConSig
import Dependent.Core.Term
import Dependent.Core.Evaluation





-- Definitions

type Definitions = [(String,Term,Term)]




-- Contexts

type Context = [(Int,Term)]




-- Unifying Type Checkers

data Equation = Equation Term Term

type MetaVar = Int

type Substitution = [(MetaVar,Term)]

data TCState
  = TCState
    { tcSig :: Signature Term
    , tcDefs :: Definitions
    , tcCtx :: Context
    , tcNextName :: Int
    , tcNextMeta :: MetaVar
    , tcSubs :: Substitution
    }

type TypeChecker a = StateT TCState (Either String) a

runTypeChecker :: TypeChecker a -> Signature Term -> Definitions -> Context -> Either String a
runTypeChecker checker sig defs ctx
  = fmap fst (runStateT checker (TCState sig defs ctx 0 0 []))

signature :: TypeChecker (Signature Term)
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
extendDefinitions edefs tc = do defs <- definitions
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

newName :: TypeChecker Int
newName = do s <- get
             put (s { tcNextName = 1 + tcNextName s })
             return $ tcNextName s

newMetaVar :: TypeChecker Term
newMetaVar = do s <- get
                put (s { tcNextMeta = 1 + tcNextMeta s })
                return $ Meta (tcNextMeta s)

substitution :: TypeChecker Substitution
substitution = tcSubs <$> get

putSubstitution :: Substitution -> TypeChecker ()
putSubstitution subs = do s <- get
                          put (s { tcSubs = subs })

occurs :: MetaVar -> Term -> Bool
occurs x (Meta y)         = x == y
occurs _ (Var _)          = False
occurs x (Ann m t)        = occurs x m || occurs x t
occurs _ Type             = False
occurs x (Fun a sc)       = occurs x a || occurs x (instantiate sc (repeat (Var undefined)))
occurs x (Lam sc)         = occurs x (instantiate sc (repeat (Var undefined)))
occurs x (App f a)        = occurs x f || occurs x a
occurs x (Con _ as)       = any (occurs x) as
occurs x (Case as mot cs) = any (occurs x) as || occursCaseMotive mot || any occursClause cs
  where
    occursCaseMotive (CaseMotiveNil m) = occurs x m
    occursCaseMotive (CaseMotiveCons a sc)
      = occurs x a || occursCaseMotive (instantiate sc (repeat (Var undefined)))
    
    occursClause (Clause _ sc) = occurs x (instantiate sc (repeat (Var undefined)))

solve :: [Equation] -> TypeChecker Substitution
solve eqs0 = go eqs0 []
  where
    go [] subs' = return subs'
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
    go (Equation (Var x) (Var y) : eqs) subs'
      = do unless (x == y)
             $ throwError $ "Cannot unify variables " ++ show (Var x)
            ++ " and " ++ show (Var y)
           go eqs subs'
    go (Equation (Ann m1 t1) (Ann m2 t2) : eqs) subs'
      = go (Equation m1 m2 : Equation t1 t2 : eqs) subs'
    go (Equation Type Type : eqs) subs'
      = go eqs subs'
    go (Equation (Fun a1 sc1) (Fun a2 sc2) : eqs) subs'
      = do i <- newName
           let b1 = instantiate sc1 [Var (Generated i)]
               b2 = instantiate sc2 [Var (Generated i)]
           go (Equation a1 a2 : Equation b1 b2 : eqs) subs'
    go (Equation (Lam sc1) (Lam sc2) : eqs) subs'
      = do i <- newName
           let b1 = instantiate sc1 [Var (Generated i)]
               b2 = instantiate sc2 [Var (Generated i)]
           go (Equation b1 b2 : eqs) subs'
    go (Equation (App f1 a1) (App f2 a2) : eqs) subs'
      = go (Equation f1 f2 : Equation a1 a2 : eqs) subs'
    go (Equation (Con c1 as1) (Con c2 as2) : eqs) subs'
      = do unless (c1 == c2)
             $ throwError $ "Mismatching constructors " ++ c1 ++ " and " ++ c2
           unless (length as1 == length as2)
             $ throwError $ "Mismatching number of arguments in "
                         ++ show (Con c1 as1) ++ " and "
                         ++ show (Con c2 as2)
           go (zipWith Equation as1 as2 ++ eqs) subs'
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
    
    goCaseMotive (CaseMotiveNil a1) (CaseMotiveNil a2)
      = return [Equation a1 a2]
    goCaseMotive (CaseMotiveCons a1 sc1) (CaseMotiveCons a2 sc2)
      = do i <- newName
           reqs <- goCaseMotive (instantiate sc1 [Var (Generated i)])
                                (instantiate sc2 [Var (Generated i)])
           return (Equation a1 a2 : reqs)
    goCaseMotive mot mot'
      = throwError $ "Motives not equal: " ++ show mot ++ " and " ++ show mot'
    
    goClauses :: [Clause] -> [Clause] -> TypeChecker [Equation]
    goClauses [] [] = return []
    goClauses (Clause ps1 sc1:cs1) (Clause ps2 sc2:cs2)
      = do xs <- goPatternSeq ps1 ps2
           reqs <- goClauses cs1 cs2
           return (Equation (instantiate sc1 xs) (instantiate sc2 xs) : reqs)
    goClauses _ _ = throwError $ "Mismatching number of clauses."
    
    goPattern :: Pattern -> Pattern -> TypeChecker [Term]
    goPattern (VarPat _) (VarPat _)
      = do i <- newName
           return [Var (Generated i)]
    goPattern (ConPat c ps) (ConPat c' ps')
      | c == c'   = goPatternSeq ps ps'
      | otherwise = throwError $ "Mismatching constructors " ++ c ++ " and " ++ c'
    goPattern _ _ = throwError "Patterns not equal."
    
    goPatternSeq :: PatternSeq -> PatternSeq -> TypeChecker [Term]
    goPatternSeq PatternSeqNil PatternSeqNil
      = return []
    goPatternSeq (PatternSeqCons p sc) (PatternSeqCons p' sc')
      = do xs <- goPattern p p'
           xs' <- goPatternSeq (instantiate sc xs) (instantiate sc' xs)
           return $ xs ++ xs'
    goPatternSeq _ _
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
           putContext (map (\(x,t) -> (x, instantiateMetas subs t)) ctx)



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
instantiateMetas subs (Ann m t)
  = Ann (instantiateMetas subs m) (instantiateMetas subs t)
instantiateMetas _ Type
  = Type
instantiateMetas subs (Fun a sc)
  = Fun (instantiateMetas subs a)
        (instantiateMetas subs <$> sc)
instantiateMetas subs (Lam sc)
  = Lam (instantiateMetas subs <$> sc)
instantiateMetas subs (App f a)
  = App (instantiateMetas subs f) (instantiateMetas subs a)
instantiateMetas subs (Con c as)
  = Con c (map (instantiateMetas subs) as)
instantiateMetas subs (Case as mot cs)
  = Case (map (instantiateMetas subs) as)
         (instantiateCaseMotive mot)
         (map instantiateClause cs)
  where
    instantiateCaseMotive (CaseMotiveNil a)
      = CaseMotiveNil (instantiateMetas subs a)
    instantiateCaseMotive (CaseMotiveCons a sc)
      = CaseMotiveCons (instantiateMetas subs a)
                       (instantiateCaseMotive <$> sc)
    
    instantiateClause (Clause ps sc)
      = Clause ps (instantiateMetas subs <$> sc)




typeInSignature :: String -> TypeChecker (ConSig Term)
typeInSignature n = do consigs <- signature
                       case lookup n consigs of
                         Nothing -> throwError $ "Unknown constructor: " ++ n
                         Just t  -> return t

typeInDefinitions :: String -> TypeChecker Term
typeInDefinitions x
  = do defs <- definitions
       case find (\(y,_,_) -> y == x) defs of
         Nothing      -> throwError $ "Unknown constant/defined term: " ++ x
         Just (_,_,t) -> return t

typeInContext :: Int -> TypeChecker Term
typeInContext i
  = do ctx <- context
       case lookup i ctx of
         Nothing -> throwError "Unbound automatically generated variable."
         Just t  -> return t

evaluate :: Term -> TypeChecker Term
evaluate m
  = do defs <- definitions
       case runReaderT (eval m) [ (x,m') | (x,m',_) <- defs ] of
         Left e   -> throwError e
         Right m' -> return m'



-- Type Inference

inferify :: Term -> TypeChecker Term
inferify (Meta i)
  = throwError $ "The metavariable " ++ show (Meta i)
              ++ " appears in checkable code, when it should not."
inferify (Var (Name x))
  = typeInDefinitions x
inferify (Var (Generated i))
  = typeInContext i
inferify (Ann m t)
  = do checkify t Type
       et <- evaluate t
       checkify m et
       subs <- substitution
       return (instantiateMetas subs et)
inferify Type
  = return Type
inferify (Fun arg sc)
  = do checkify arg Type
       i <- newName
       extendContext [(i,arg)]
         $ checkify (instantiate sc [Var (Generated i)]) Type
       return Type
inferify (Lam _)
  = throwError "Cannot infer the type of a lambda expression."
inferify (App f a)
  = do t <- inferify f
       et <- evaluate t
       case et of
         Fun arg sc -> do
           earg <- evaluate arg
           checkify a earg
           return (instantiate sc [a])
         _ -> throwError $ "Cannot apply non-function: " ++ show f
inferify (Con c as)
  = do consig <- typeInSignature c
       inferifyConArgs consig as consig
  where
    inferifyConArgs _ [] (ConSigNil ret)
      = do sub <- substitution
           return $ instantiateMetas sub ret
    inferifyConArgs consig (m:ms) (ConSigCons arg sc)
      = do subs <- substitution
           earg <- evaluate (instantiateMetas subs arg)
           checkify m earg
           inferifyConArgs consig ms (instantiate sc [m])
    inferifyConArgs consig _ _
      = do let las = length as
               lsig = conSigLength (Var . Name) consig
           throwError $ c ++ " expects " ++ show lsig ++ " "
                   ++ (if lsig == 1 then "arg" else "args")
                   ++ " but was given " ++ show las
inferify (Case ms0 mot cs)
  = do checkifyCaseMotive mot
       checkifyCaseArgs ms0 mot
       checkifyClauses cs mot
       auxMotive ms0 mot
  where
    checkifyCaseArgs [] (CaseMotiveNil _)
      = return ()
    checkifyCaseArgs (m:ms) (CaseMotiveCons a sc)
      = do ea <- evaluate a
           checkify m ea
           checkifyCaseArgs ms (instantiate sc [m])
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

checkify :: Term -> Term -> TypeChecker ()
checkify (Meta i) _
  = throwError $ "The metavariable " ++ show (Meta i)
              ++ " appears in checkable code, when it should not."
checkify (Lam sc) t
  = do et <- evaluate t
       case et of
         Fun arg sc' -> do
           i <- newName
           eret <- evaluate (instantiate sc' [Var (Generated i)])
           extendContext [(i,arg)]
             $ checkify
                 (instantiate sc [Var (Generated i)])
                 eret
         _ -> throwError $ "Cannot check term: " ++ show (Lam sc) ++ "\n"
              ++ "Against non-function type: " ++ show t
checkify m t
  = do t' <- inferify m
       et <- evaluate t
       et' <- evaluate t'
       unify et et'


checkifyCaseMotive :: CaseMotive -> TypeChecker ()
checkifyCaseMotive (CaseMotiveNil a)
  = checkify a Type
checkifyCaseMotive (CaseMotiveCons a sc)
  = do checkify a Type
       i <- newName
       extendContext [(i,a)]
         $ checkifyCaseMotive (instantiate sc [Var (Generated i)])


checkifyPattern :: Pattern -> Term -> TypeChecker (Context,Term)
checkifyPattern (VarPat _) t
  = do i <- newName
       return ([(i,t)], Var (Generated i))
checkifyPattern (ConPat c ps) t
  = do sig <- typeInSignature c
       (ctx,xs,ret) <- checkifyPatConArgs sig ps sig
       et <- evaluate t
       eret <- evaluate ret
       unify et eret
       return (ctx, Con c xs)
  where
    checkifyPatConArgs _ PatternSeqNil (ConSigNil ret)
      = return ([],[],ret)
    checkifyPatConArgs consig (PatternSeqCons p sc) (ConSigCons arg sc')
      = do earg <- evaluate arg
           (ctx,x) <- checkifyPattern p earg
           let is = [ Var (Generated i) | (i,_) <- ctx ]
           (ctx',xs,ret) <-
             extendContext ctx
               $ checkifyPatConArgs consig (instantiate sc is) (instantiate sc' [x])
           return (ctx++ctx', x:xs, ret)
    checkifyPatConArgs consig _ _
      = do let lps = patternSeqLength ps
               lsig = conSigLength (Var . Name) consig
           throwError $ c ++ " expects " ++ show lsig ++ " case "
                   ++ (if lsig == 1 then "arg" else "args")
                   ++ " but was given " ++ show lps
checkifyPattern (AssertionPat m) t
  = do et <- evaluate t
       checkify m et
       return ([], m)


checkifyPatterns :: [Pattern] -> CaseMotive -> TypeChecker (Context,[Term],Term)
checkifyPatterns [] (CaseMotiveNil a)
  = return ([],[],a)
checkifyPatterns (p:ps) (CaseMotiveCons a sc)
  = do ea <- evaluate a
       (ctx,m) <- checkifyPattern p ea
       (ctx',ms,t) <- checkifyPatterns ps (instantiate sc [m])
       return (ctx++ctx', m:ms, t)
checkifyPatterns _ _
  = throwError "Mismatching length of patterns and case motive args."


checkifyClause :: Clause -> CaseMotive -> TypeChecker ()
checkifyClause (Clause ps sc0) motive
  = do (ctx,ret) <- checkPatternSeqMotive ps motive
       let xs = [ Var (Generated i) | (i,_) <- ctx ]
       eret <- evaluate ret
       extendContext ctx
         $ checkify (instantiate sc0 xs) eret
  where
    checkPatternSeqMotive :: PatternSeq -> CaseMotive -> TypeChecker (Context,Term)
    checkPatternSeqMotive PatternSeqNil (CaseMotiveNil ret)
      = return ([],ret)
    checkPatternSeqMotive (PatternSeqCons p sc) (CaseMotiveCons arg sc')
      = do earg <- evaluate arg
           (ctx,x) <- checkifyPattern p earg
           let is = [ Var (Generated i) | (i,_) <- ctx ]
           (ctx',ret) <-
             extendContext ctx
               $ checkPatternSeqMotive (instantiate sc is) (instantiate sc' [x])
           return (ctx++ctx',ret)
    checkPatternSeqMotive _ _
      = do let lps = patternSeqLength ps
               lmot = caseMotiveLength motive
           throwError $ "Motive " ++ show motive ++ " expects " ++ show lmot ++ " case "
                   ++ (if lmot == 1 then "arg" else "args")
                   ++ " but was given " ++ show lps


checkifyClauses :: [Clause] -> CaseMotive -> TypeChecker ()
checkifyClauses [] _
  = return ()
checkifyClauses (c:cs) motive
  = do checkifyClause c motive
       checkifyClauses cs motive

checkifyConSig :: ConSig Term -> TypeChecker ()
checkifyConSig (ConSigNil ret)
  = checkify ret Type
checkifyConSig (ConSigCons arg sc)
  = do checkify arg Type
       i <- newName
       extendContext [(i,arg)]
         $ checkifyConSig (instantiate sc [Var (Generated i)])




-- type checking succees exactly when checkification succeeds
-- and there is a substitution for every meta-variable


metasSolved :: TypeChecker ()
metasSolved = do s <- get
                 unless (tcNextMeta s == length (tcSubs s))
                   $ throwError "Not all metavariables have been solved."

check :: Term -> Term -> TypeChecker ()
check m t = do et <- evaluate t
               checkify m et
               metasSolved
                
infer :: Term -> TypeChecker Term
infer m = do t <- inferify m
             metasSolved
             subs <- substitution
             et <- evaluate (instantiateMetas subs t)
             return et