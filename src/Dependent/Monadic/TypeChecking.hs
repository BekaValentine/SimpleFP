{-# OPTIONS -Wall #-}

module Dependent.Monadic.TypeChecking where

import Control.Applicative ((<$>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List (find)

import Eval
import Scope
import Dependent.Core.ConSig
import Dependent.Core.Evaluation ()
import Dependent.Core.Term




apM2 :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
apM2 f ma mb = do a <- ma
                  b <- mb
                  f a b




-- Definitions

type Definitions = [(String,Term,Term)]




-- Contexts

type Context = [(Int,Term)]




-- Type Checking Monad

data TCState
  = TCState
    { tcSig :: Signature Term
    , tcDefs :: Definitions
    , tcCtx :: Context
    , tcNextName :: Int
    }

type TypeChecker a = StateT TCState (Either String) a

runTypeChecker :: TypeChecker a -> Signature Term -> Definitions -> Context -> Either String a
runTypeChecker tc sig defs ctx
  = fmap fst (runStateT tc (TCState sig defs ctx 0))

signature :: TypeChecker (Signature Term)
signature = tcSig <$> get

definitions :: TypeChecker Definitions
definitions = tcDefs <$> get

context :: TypeChecker Context
context = tcCtx <$> get

extendDefinitions :: Definitions -> TypeChecker a -> TypeChecker a
extendDefinitions edefs tc
  = do s <- get
       put (s { tcDefs = edefs ++ tcDefs s })
       x <- tc
       put s
       return x

extendContext :: Context -> TypeChecker a -> TypeChecker a
extendContext ectx tc
  = do s <- get
       put (s { tcCtx = ectx ++ tcCtx s })
       x <- tc
       put s
       return x

newName :: TypeChecker Int
newName = do s <- get
             put (s { tcNextName = 1 + tcNextName s })
             return $ tcNextName s

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
       equalTerms (instantiate sc [Var (Generated i)])
                  (instantiate sc' [Var (Generated i)])
equalTerms (Lam sc) (Lam sc')
  = do i <- newName
       equalTerms (instantiate sc [Var (Generated i)])
                  (instantiate sc' [Var (Generated i)])
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
           equalCaseMotives (instantiate sc [Var (Generated i)])
                            (instantiate sc' [Var (Generated i)])
    equalCaseMotives mot mot'
      = throwError $ "Motives not equal: " ++ show mot ++ " and " ++ show mot'
    
    equalClauses :: Clause -> Clause -> TypeChecker ()
    equalClauses (Clause ps sc) (Clause ps' sc')
      = do xs <- equalPatternSeq ps ps'
           equalTerms (instantiate sc xs) (instantiate sc' xs)
    
    equalPattern :: Pattern -> Pattern -> TypeChecker [Term]
    equalPattern VarPat VarPat
      = do i <- newName
           return [Var (Generated i)]
    equalPattern (ConPat c ps) (ConPat c' ps')
      = do unless (c == c')
             $ throwError $ "Mismatching constructors " ++ c ++ " and " ++ c'
           equalPatternSeq ps ps'
    equalPattern (AssertionPat m) (AssertionPat m')
      = do equalTerms m m'
           return []
    equalPattern p p'
      = throwError $ "Patterns not equal: " ++ show p ++ " and " ++ show p'
    
    equalPatternSeq :: PatternSeq -> PatternSeq -> TypeChecker [Term]
    equalPatternSeq PatternSeqNil PatternSeqNil
      = return []
    equalPatternSeq (PatternSeqCons p sc) (PatternSeqCons p' sc')
      = do xs <- equalPattern p p'
           xs' <- equalPatternSeq (instantiate sc xs) (instantiate sc' xs)
           return $ xs ++ xs'
    equalPatternSeq ps ps'
      = throwError $ "Pattern sequences not equal: " ++ show ps ++ " and " ++ show ps'
equalTerms m m'
  = throwError $ "Terms not equal: " ++ show m ++ " and " ++ show m'



-- Type Inference

infer :: Term -> TypeChecker Term
infer (Meta _) = error "Meta variables should not exist in this type checker."
infer (Var (Name x))
  = typeInDefinitions x
infer (Var (Generated i))
  = typeInContext i
infer (Ann m t)
  = do check t Type
       check m t
       return t
infer Type
  = return Type
infer (Fun arg sc)
  = do check arg Type
       i <- newName
       extendContext [(i,arg)]
         $ check (instantiate sc [Var (Generated i)]) Type
       return Type
infer (Lam _)
  = throwError "Cannot infer the type of a lambda expression."
infer (App f a)
  = do Fun arg sc <- infer f
       check a arg
       return (instantiate sc [a])
infer (Con c as)
  = do consig <- typeInSignature c
       inferConArgs consig as consig
  where
    inferConArgs _ [] (ConSigNil ret)
      = return ret
    inferConArgs consig (m:ms) (ConSigCons arg sc)
      = do check m arg
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
      = do check a arg
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
           extendContext [(i,arg)]
             $ check (instantiate sc [Var (Generated i)])
                     (instantiate sc' [Var (Generated i)])
         _ -> throwError $ "Cannot check term: " ++ show (Lam sc) ++ "\n"
              ++ "Against non-function type: " ++ show t
check m t
  = do t' <- infer m
       apM2 equalTerms (evaluate t') (evaluate t)

checkCaseMotive :: CaseMotive -> TypeChecker ()
checkCaseMotive (CaseMotiveNil ret)
  = check ret Type
checkCaseMotive (CaseMotiveCons arg sc)
  = do check arg Type
       i <- newName
       extendContext [(i,arg)]
         $ checkCaseMotive (instantiate sc [Var (Generated i)])

checkPattern :: Pattern -> Term -> TypeChecker (Context,Term)
checkPattern VarPat t
  = do i <- newName
       return ([(i,t)], Var (Generated i))
checkPattern (ConPat c ps) t
  = do consig <- typeInSignature c
       (ctx,xs,ret) <- checkPatConArgs consig ps consig
       apM2 equalTerms (evaluate ret) (evaluate t)
       return (ctx,Con c xs)
  where
    checkPatConArgs _ PatternSeqNil (ConSigNil ret)
      = return ([], [], ret)
    checkPatConArgs consig (PatternSeqCons p sc) (ConSigCons arg sc')
      = do (ctx,x) <- checkPattern p arg
           let is = [ Var (Generated i) | (i,_) <- ctx ]
           (ctx',xs,ret) <-
             extendContext ctx
               $ checkPatConArgs consig (instantiate sc is) (instantiate sc' [x])
           return (ctx++ctx',x:xs,ret)
    checkPatConArgs consig _ _
      = do let lps = patternSeqLength ps
               lsig = conSigLength (Var . Name) consig
           throwError $ c ++ " expects " ++ show lsig ++ " case "
                   ++ (if lsig == 1 then "arg" else "args")
                   ++ " but was given " ++ show lps
checkPattern (AssertionPat m) t
  = do check m t
       return ([], m)

checkClause :: Clause -> CaseMotive -> TypeChecker ()
checkClause (Clause ps sc0) motive
  = do (ctx,xs,ret) <- checkPatternSeqMotive ps motive
       extendContext ctx
         $ check (instantiate sc0 xs) ret
  where
    checkPatternSeqMotive :: PatternSeq -> CaseMotive -> TypeChecker (Context,[Term],Term)
    checkPatternSeqMotive PatternSeqNil (CaseMotiveNil ret)
      = return ([],[],ret)
    checkPatternSeqMotive (PatternSeqCons p sc) (CaseMotiveCons arg sc')
      = do (ctx,x) <- checkPattern p arg
           let is = [ Var (Generated i) | (i,_) <- ctx ]
           (ctx',xs,ret) <-
             extendContext ctx
               $ checkPatternSeqMotive (instantiate sc is) (instantiate sc' [x])
           return (ctx++ctx',x:xs,ret)
    checkPatternSeqMotive _ _
      = do let lps = patternSeqLength ps
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
       extendContext [(i,arg)]
         $ checkConSig (instantiate sc [Var (Generated i)])