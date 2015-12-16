{-# OPTIONS -Wall #-}
{-# LANGUAGE TypeFamilies #-}

module Dependent.Monadic.TypeChecking where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List (find)

import Eval
import Scope
import TypeChecker
import Dependent.Core.ConSig
import Dependent.Core.Evaluation ()
import Dependent.Core.Term




-- Definitions

type Definitions = [(String,Term,Term)]




-- Contexts

type Context = [(Int,String,Term)]




-- Type Checking Monad

data TCState
  = TCState
    { tcSig :: Signature Term
    , tcDefs :: Definitions
    , tcCtx :: Context
    , tcNextName :: Int
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

type TypeChecker a = StateT TCState (Either String) a

runTypeChecker :: TypeChecker a -> Signature Term -> Definitions -> Context -> Int -> Either String (a,TCState)
runTypeChecker tc sig defs ctx i
  = runStateT tc (TCState sig defs ctx i)

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
       case find (\(j,_,_) -> j == i) ctx of
         Nothing      -> throwError "Unbound automatically generated variable."
         Just (_,_,t) -> return t

evaluate :: Term -> TypeChecker Term
evaluate m
  = do defs <- definitions
       case runReaderT (eval m) [ (x,m') | (x,m',_) <- defs ] of
         Left e   -> throwError e
         Right m' -> return m'




-- Term equality

equalTerms :: Term -> Term -> TypeChecker ()
equalTerms (Meta _) _ = throwError "Meta variables should not exist in this type checker."
equalTerms _ (Meta _) = throwError "Meta variables should not exist in this type checker."
equalTerms (Var x) (Var x')
  = unless (x == x')
      $ throwError $ "Variables not equal: " ++ show x ++ " and " ++ show x'
equalTerms (Ann m t) (Ann m' t')
  = do equalTerms m m'
       equalTerms t t'
equalTerms Type Type
  = return ()
equalTerms (Fun arg sc) (Fun arg' sc')
  = do equalTerms arg arg'
       i <- newName
       equalTerms (instantiate sc [Var (Generated (head (names sc)) i)])
                  (instantiate sc' [Var (Generated (head (names sc')) i)])
equalTerms (Lam sc) (Lam sc')
  = do i <- newName
       equalTerms (instantiate sc [Var (Generated (head (names sc)) i)])
                  (instantiate sc' [Var (Generated (head (names sc')) i)])
equalTerms (App f a) (App f' a')
  = do equalTerms f f'
       equalTerms a a'
equalTerms (Con c as) (Con c' as')
  = do unless (c == c')
         $ throwError $ "Mismatching constructors " ++ c ++ " and " ++ c'
       unless (length as == length as')
         $ throwError $ "Mismatching number of arguments in "
                     ++ show (Con c as) ++ " and "
                     ++ show (Con c' as')
       zipWithM_ equalTerms as as'
equalTerms (Case as motive cs) (Case as' motive' cs')
  = do unless(length as == length as')
         $ throwError $ "Mismatching number of case arguments in "
                     ++ show (Case as motive cs) ++ " and "
                     ++ show (Case as' motive' cs')
       unless (length cs == length cs')
         $ throwError $ "Mismatching number of clauses in "
                     ++ show (Case as motive cs) ++ " and "
                     ++ show (Case as' motive' cs')
       zipWithM_ equalTerms as as'
       equalCaseMotives motive motive'
       zipWithM_ equalClauses cs cs'
  where
    equalCaseMotives :: CaseMotive -> CaseMotive -> TypeChecker ()
    equalCaseMotives (CaseMotiveNil b) (CaseMotiveNil b')
      = equalTerms b b'
    equalCaseMotives (CaseMotiveCons a sc) (CaseMotiveCons a' sc')
      = do equalTerms a a'
           i <- newName
           equalCaseMotives (instantiate sc [Var (Generated (head (names sc)) i)])
                            (instantiate sc' [Var (Generated (head (names sc')) i)])
    equalCaseMotives mot mot'
      = throwError $ "Motives not equal: " ++ show mot ++ " and " ++ show mot'
    
    equalClauses :: Clause -> Clause -> TypeChecker ()
    equalClauses (Clause psc sc) (Clause psc' sc')
      = do unless (length (names psc) == length (names psc'))
             $ throwError "Patterns bind different numbers of arguments."
           is <- replicateM (length (names psc)) newName
           let xs0 = zipWith Generated (names psc) is
               xs0' = map Var xs0
               xs1 = zipWith Generated (names psc') is
               xs1' = map Var xs1
           zipWithM_ equalPattern (instantiate psc xs0) (instantiate psc' xs1)
           equalTerms (instantiate sc (removeByDummies (names psc) xs0')) (instantiate sc' (removeByDummies (names psc') xs1'))
    
    equalPattern :: Pattern -> Pattern -> TypeChecker ()
    equalPattern (VarPat x) (VarPat x')
      = unless (x == x')
          $ throwError $ "Variable patterns not equal: " ++ show x ++ " and " ++ show x'
    equalPattern (ConPat c ps) (ConPat c' ps')
      = do unless (c == c')
             $ throwError $ "Mismatching constructors " ++ c ++ " and " ++ c'
           zipWithM_ equalPattern ps ps'
    equalPattern (AssertionPat m) (AssertionPat m')
      = equalTerms m m'
    equalPattern p p'
      = throwError $ "Patterns not equal: " ++ show p ++ " and " ++ show p'
equalTerms m m'
  = throwError $ "Terms not equal: " ++ show m ++ " and " ++ show m'



-- Type Inference

infer :: Term -> TypeChecker Term
infer (Meta _) = error "Meta variables should not exist in this type checker."
infer (Var (Name x))
  = typeInDefinitions x
infer (Var (Generated _ i))
  = typeInContext i
infer (Ann m t)
  = do check t Type
       et <- evaluate t
       check m et
       return et
infer Type
  = return Type
infer (Fun arg sc)
  = do check arg Type
       i <- newName
       extendContext [(i, head (names sc), arg)]
         $ check (instantiate sc [Var (Generated (head (names sc)) i)]) Type
       return Type
infer (Lam _)
  = throwError "Cannot infer the type of a lambda expression."
infer (App f a)
  = do t <- infer f
       et <- evaluate t
       case et of
         Fun arg sc -> do
           earg <- evaluate arg
           check a earg
           return (instantiate sc [a])
         _ -> throwError $ "Cannot apply a non-function: " ++ show f
infer (Con c as)
  = do consig <- typeInSignature c
       inferConArgs consig as consig
  where
    inferConArgs _ [] (ConSigNil ret)
      = return ret
    inferConArgs consig (m:ms) (ConSigCons arg sc)
      = do earg <- evaluate arg
           check m earg
           inferConArgs consig ms (instantiate sc [m])
    inferConArgs consig _ _
      = do let las = length as
               lsig = conSigLength (Var . Name) consig
           throwError $ c ++ " expects " ++ show lsig ++ " "
                   ++ (if lsig == 1 then "arg" else "args")
                   ++ " but was given " ++ show las
infer (Case as0 motive cs)
  = do checkCaseMotive motive
       checkCaseArgs as0 motive
       checkClauses cs motive
       auxMotive as0 motive
  where
    checkCaseArgs [] (CaseMotiveNil _)
      = return ()
    checkCaseArgs (a:as) (CaseMotiveCons arg sc)
      = do earg <- evaluate arg
           check a earg
           checkCaseArgs as (instantiate sc [a])
    checkCaseArgs _ _
      = do let las = length as0
               lmot = caseMotiveLength motive
           throwError $ "Motive " ++ show motive ++ " expects " ++ show lmot ++ " case "
                   ++ (if lmot == 1 then "arg" else "args")
                   ++ " but was given " ++ show las
    
    auxMotive [] (CaseMotiveNil ret)
      = return ret
    auxMotive (m:ms) (CaseMotiveCons _ sc)
      = auxMotive ms (instantiate sc [m])
    auxMotive _ _
      = do let las = length as0
               lmot = caseMotiveLength motive
           throwError $ "Motive " ++ show motive ++ " expects " ++ show lmot ++ " case "
                   ++ (if lmot == 1 then "arg" else "args")
                   ++ " but was given " ++ show las




-- Type Checking

check :: Term -> Term -> TypeChecker ()
check (Meta _) _ = error "Meta variables should exist in this type checker."
check (Lam sc) t
  = do et <- evaluate t
       case et of
         Fun arg sc' -> do
           check arg Type
           i <- newName
           eret <- evaluate (instantiate sc' [Var (Generated (head (names sc)) i)])
           extendContext [(i, head (names sc), arg)]
             $ check (instantiate sc [Var (Generated (head (names sc)) i)])
                     eret
         _ -> throwError $ "Cannot check term: " ++ show (Lam sc) ++ "\n"
              ++ "Against non-function type: " ++ show t
check m t
  = do t' <- infer m
       et <- evaluate t
       et' <- evaluate t'
       equalTerms et et'

checkCaseMotive :: CaseMotive -> TypeChecker ()
checkCaseMotive (CaseMotiveNil ret)
  = check ret Type
checkCaseMotive (CaseMotiveCons arg sc)
  = do check arg Type
       i <- newName
       extendContext [(i, head (names sc), arg)]
         $ checkCaseMotive (instantiate sc [Var (Generated (head (names sc)) i)])

checkPattern :: Pattern -> Term -> TypeChecker (Context,Term,[(Term,Term)])
checkPattern (VarPat (Name x)) _
  = return ([], Var (Name x), [])
checkPattern (VarPat (Generated x i)) t
  = return ([(i,x,t)], Var (Generated x i), [])
checkPattern (ConPat _ _) Type
  = throwError "Cannot pattern match on a type."
checkPattern (ConPat c ps0) t
  = do consig <- typeInSignature c
       (ctx,xs,ret,delayed) <- checkPatConArgs consig ps0 consig
       eret <- evaluate ret
       et <- evaluate t
       equalTerms eret et
       return (ctx,Con c xs,delayed)
  where
    checkPatConArgs _ [] (ConSigNil ret)
      = return ([], [], ret, [])
    checkPatConArgs consig (p:ps) (ConSigCons arg sc')
      = do (ctx,x,delayed) <- checkPattern p arg
           (ctx',xs,ret,delayed') <-
             extendContext ctx
               $ checkPatConArgs consig ps (instantiate sc' [x])
           return (ctx++ctx',x:xs,ret,delayed++delayed')
    checkPatConArgs consig _ _
      = do let lps = length ps0
               lsig = conSigLength (Var . Name) consig
           throwError $ c ++ " expects " ++ show lsig ++ " case "
                   ++ (if lsig == 1 then "arg" else "args")
                   ++ " but was given " ++ show lps
checkPattern (AssertionPat m) t
  = return ([], m, [(m,t)])

checkClause :: Clause -> CaseMotive -> TypeChecker ()
checkClause (Clause psc sc0) motive
  = do is <- replicateM (length (names psc)) newName
       let xs1 = zipWith Generated (names psc) is
           xs2 = map Var (removeByDummies (names psc) xs1)
       (ctx,ret,delayed) <- checkPatternSeqMotive (instantiate psc xs1) motive
       forM_ delayed $ \(m,t) -> extendContext ctx (check m t)
       eret <- evaluate ret
       extendContext ctx
         $ check (instantiate sc0 xs2) eret
  where
    checkPatternSeqMotive :: [Pattern] -> CaseMotive -> TypeChecker (Context,Term,[(Term,Term)])
    checkPatternSeqMotive [] (CaseMotiveNil ret)
      = return ([],ret,[])
    checkPatternSeqMotive (p:ps) (CaseMotiveCons arg sc')
      = do (ctx,x,delayed) <- checkPattern p arg
           (ctx',ret,delayed') <-
             extendContext ctx
               $ checkPatternSeqMotive ps (instantiate sc' [x])
           return (ctx++ctx',ret,delayed++delayed')
    checkPatternSeqMotive _ _
      = do let lps = length (descope Name psc)
               lmot = caseMotiveLength motive
           throwError $ "Motive " ++ show motive ++ " expects " ++ show lmot ++ " case "
                   ++ (if lmot == 1 then "arg" else "args")
                   ++ " but was given " ++ show lps

checkClauses :: [Clause] -> CaseMotive -> TypeChecker ()
checkClauses [] _
  = return ()
checkClauses (c:cs) motive
  = do checkClause c motive
       checkClauses cs motive

checkConSig :: ConSig Term -> TypeChecker ()
checkConSig (ConSigNil ret)
  = check ret Type
checkConSig (ConSigCons arg sc)
  = do check arg Type
       i <- newName
       extendContext [(i, head (names sc), arg)]
         $ checkConSig (instantiate sc [Var (Generated (head (names sc)) i)])