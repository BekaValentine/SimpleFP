{-# OPTIONS -Wall #-}

module Dependent.Monadic.TypeChecking where

import System.IO.Unsafe
import Control.Applicative ((<$>))
import Control.Monad.Reader
import Control.Monad.State
import Data.List (find)

import Env
import Eval
import Scope
import Dependent.Core.ConSig
import Dependent.Core.Evaluation
import Dependent.Core.Term




apM2 :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
apM2 f ma mb = do a <- ma
                  b <- mb
                  f a b




-- Definitions

type Definitions = [(String,Term,Term)]

definitionsToEnvironment :: Definitions -> Environment String Term
definitionsToEnvironment defs
  = [ (x,m) | (x,m,_) <- defs ]




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

type TypeChecker a = StateT TCState Maybe a

runTypeChecker :: TypeChecker a -> Signature Term -> Definitions -> Context -> Maybe a
runTypeChecker tc sig defs ctx
  = fmap fst (runStateT tc (TCState sig defs ctx 0))

failure :: TypeChecker a
failure = StateT $ \_ -> Nothing

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
                         Nothing -> failure
                         Just t  -> return t

typeInDefinitions :: String -> TypeChecker Term
typeInDefinitions x
  = do defs <- definitions
       case find (\(y,_,_) -> y == x) defs of
         Nothing      -> failure
         Just (_,_,t) -> return t

typeInContext :: Int -> TypeChecker Term
typeInContext i
  = do ctx <- context
       case lookup i ctx of
         Nothing -> failure
         Just t  -> return t

evaluate :: Term -> TypeChecker Term
evaluate m
  = do defs <- definitions
       case runReaderT (eval m) (definitionsToEnvironment defs) of
         Left _   -> failure
         Right m' -> return m'




-- Term equality

equalTerms :: Term -> Term -> TypeChecker ()
equalTerms (Meta _) _ = error "Meta variables should not exist in this type checker."
equalTerms _ (Meta _) = error "Meta variables should not exist in this type checker."
equalTerms (Var x) (Var x')
  = guard $ x == x'
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
  = do guard $ c == c' && length as == length as'
       zipWithM_ equalTerms as as'
equalTerms (Case as motive cs) (Case as' motive' cs')
  = do guard $ length as == length as' && length cs == length cs'
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
    equalCaseMotives _ _
      = failure
    
    equalClauses :: Clause -> Clause -> TypeChecker ()
    equalClauses (Clause ps sc) (Clause ps' sc')
      = do xs <- equalPatternSeq ps ps'
           equalTerms (instantiate sc xs) (instantiate sc' xs)
    
    equalPattern :: Pattern -> Pattern -> TypeChecker [Term]
    equalPattern VarPat VarPat
      = do i <- newName
           return [Var (Generated i)]
    equalPattern (ConPat c ps) (ConPat c' ps')
      = do guard $ c == c'
           equalPatternSeq ps ps'
    equalPattern (AssertionPat m) (AssertionPat m')
      = do equalTerms m m'
           return []
    equalPattern _ _
      = failure
    
    equalPatternSeq :: PatternSeq -> PatternSeq -> TypeChecker [Term]
    equalPatternSeq PatternSeqNil PatternSeqNil
      = return []
    equalPatternSeq (PatternSeqCons p sc) (PatternSeqCons p' sc')
      = do xs <- equalPattern p p'
           xs' <- equalPatternSeq (instantiate sc xs) (instantiate sc' xs)
           return $ xs ++ xs'
    equalPatternSeq _ _
      = failure
equalTerms _ _
  = failure



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
  = failure
infer (App f a)
  = do Fun arg sc <- infer f
       check a arg
       return (instantiate sc [a])
infer (Con c as)
  = do consig <- typeInSignature c
       inferConArgs as consig
  where
    inferConArgs [] (ConSigNil ret)
      = return ret
    inferConArgs (m:ms) (ConSigCons arg sc)
      = do check m arg
           inferConArgs ms (instantiate sc [m])
    inferConArgs _ _
      = failure
infer (Case as motive cs)
  = do checkCaseMotive motive
       checkCaseArgs as motive
       checkClauses cs motive
       auxMotive as motive
  where
    auxMotive [] (CaseMotiveNil ret)
      = return ret
    auxMotive (m:ms) (CaseMotiveCons _ sc)
      = auxMotive ms (instantiate sc [m])
    auxMotive _ _
      = failure




-- Type Checking

check :: Term -> Term -> TypeChecker ()
check (Meta _) _ = error "Meta variables should exist in this type checker."
check (Var (Name x)) t
  = do t' <- infer (Var (Name x))
       apM2 equalTerms (evaluate t') (evaluate t)
check (Var (Generated i)) t
  = do t' <- infer (Var (Generated i))
       apM2 equalTerms (evaluate t') (evaluate t)
check (Ann m t') t
  = do t'' <- infer (Ann m t')
       apM2 equalTerms (evaluate t'') (evaluate t)
check Type t
  = do t' <- infer Type
       apM2 equalTerms (evaluate t') (evaluate t)
check (Fun arg sc) t
  = do t' <- infer (Fun arg sc)
       apM2 equalTerms (evaluate t') (evaluate t)
check (Lam sc) t
  = do et <- evaluate t
       case et of
         Fun arg sc' -> do
           check arg Type
           i <- newName
           extendContext [(i,arg)]
             $ check (instantiate sc [Var (Generated i)])
                     (instantiate sc' [Var (Generated i)])
         _ -> failure
check (App f a) t
  = do t' <- infer (App f a)
       apM2 equalTerms (evaluate t') (evaluate t)
check (Con c as) t
  = do t' <- infer (Con c as)
       apM2 equalTerms (evaluate t') (evaluate t)
check (Case as motive cs) t
  = do t' <- infer (Case as motive cs)
       apM2 equalTerms (evaluate t') (evaluate t)

checkCaseMotive :: CaseMotive -> TypeChecker ()
checkCaseMotive (CaseMotiveNil ret)
  = check ret Type
checkCaseMotive (CaseMotiveCons arg sc)
  = do check arg Type
       i <- newName
       extendContext [(i,arg)]
         $ checkCaseMotive (instantiate sc [Var (Generated i)])

checkCaseArgs :: [Term] -> CaseMotive -> TypeChecker ()
checkCaseArgs [] (CaseMotiveNil _)
  = return ()
checkCaseArgs (a:as) (CaseMotiveCons arg sc)
  = do check a arg
       checkCaseArgs as (instantiate sc [a])
checkCaseArgs _ _
  = failure

checkPattern :: Pattern -> Term -> TypeChecker (Context,Term)
checkPattern VarPat t
  = do i <- newName
       return ([(i,t)], Var (Generated i))
checkPattern (ConPat c ps) t
  = do consig <- typeInSignature c
       (ctx,xs,ret) <- checkPatConArgs ps consig
       apM2 equalTerms (evaluate ret) (evaluate t)
       return (ctx,Con c xs)
  where
    checkPatConArgs :: PatternSeq -> ConSig Term -> TypeChecker (Context,[Term],Term)
    checkPatConArgs PatternSeqNil (ConSigNil ret)
      = return ([], [], ret)
    checkPatConArgs (PatternSeqCons p sc) (ConSigCons arg sc')
      = do (ctx,x) <- checkPattern p arg
           let is = [ Var (Generated i) | (i,_) <- ctx ]
           (ctx',xs,ret) <-
             extendContext ctx
               $ checkPatConArgs (instantiate sc is) (instantiate sc' [x])
           return (ctx++ctx',x:xs,ret)
    checkPatConArgs _ _
      = failure
checkPattern (AssertionPat m) t
  = do check m t
       return ([], m)

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
  = failure

checkClause :: Clause -> CaseMotive -> TypeChecker ()
checkClause (Clause ps sc) motive
  = do (ctx,xs,ret) <- checkPatternSeqMotive ps motive
       extendContext ctx
         $ check (instantiate sc xs) ret

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