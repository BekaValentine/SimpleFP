{-# OPTIONS -Wall #-}
{-# LANGUAGE TypeFamilies #-}

module Simple.Monadic.TypeChecking where

import Control.Monad.Except
import Control.Monad.State
import Data.List (intercalate,find)

import Env
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




-- Definitions

type Definitions = [(String,Term,Type)]

definitionsToEnvironment :: Definitions -> Environment String Term
definitionsToEnvironment defs
  = [ (x,m) | (x,m,_) <- defs ]




-- Contexts

type Context = [(Int,Type)]




-- Type Checking Monad

data TCState
  = TCState
    { tcSig :: Signature
    , tcDefs :: Definitions
    , tcCtx :: Context
    , tcNextName :: Int
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

type TypeChecker a = StateT TCState (Either String) a

runTypeChecker :: TypeChecker a -> Signature -> Definitions -> Context -> Int -> Either String (a,TCState)
runTypeChecker tc sig defs ctx i
  = runStateT tc (TCState sig defs ctx i)

tyconExists :: String -> TypeChecker ()
tyconExists n
  = do Signature tycons _ <- signature
       unless (n `elem` tycons)
         $ throwError $ "Unknown type constructor: " ++ n

typeInSignature :: String -> TypeChecker ConSig
typeInSignature n
  = do Signature _ consigs <- signature
       case lookup n consigs of
         Nothing -> throwError $ "Unknown constructor: " ++ n
         Just t  -> return t

typeInDefinitions :: String -> TypeChecker Type
typeInDefinitions x
  = do defs <- definitions
       case find (\(y,_,_) -> y == x) defs of
         Nothing      -> throwError $ "Unknown constant/defined term: " ++ x
         Just (_,_,t) -> return t

typeInContext :: Int -> TypeChecker Type
typeInContext i
  = do ctx <- context
       case lookup i ctx of
         Nothing -> throwError "Unbound automatically generated variable."
         Just t  -> return t



-- Type well-formedness

isType :: Type -> TypeChecker ()
isType (TyCon tc) = tyconExists tc
isType (Fun a b)  = isType a >> isType b
isType (Meta _)   = throwError "Meta variables should not be present in the this type checker."



-- Type Inference

infer :: Term -> TypeChecker Type
infer (Var (Name x))
  = typeInDefinitions x
infer (Var (Generated i))
  = typeInContext i
infer (Ann m t)
  = check m t >> return t
infer (Lam _)
  = throwError "Cannot infer the type of a lambda expression."
infer (App f a)
  = do Fun arg ret <- infer f
       check a arg
       return ret
infer (Con c as)
  = do ConSig args ret <- typeInSignature c
       let las = length as
           largs = length args
       unless (las == largs)
         $ throwError $ c ++ " expects " ++ show largs ++ " "
                   ++ (if largs == 1 then "arg" else "args")
                   ++ " but was given " ++ show las
       zipWithM_ check as args
       return ret
infer (Case m cs)
  = do t <- infer m
       inferClauses t cs


inferClause :: Type -> Clause -> TypeChecker Type
inferClause patTy (Clause p sc)
  = do ctx' <- checkPattern p patTy
       let xs = [ Var (Generated i) | (i,_) <- ctx' ]
       extendContext ctx'
         $ infer (instantiate sc xs)

inferClauses :: Type -> [Clause] -> TypeChecker Type
inferClauses patTy cs
  = do ts <- mapM (inferClause patTy) cs
       case ts of
         [] -> throwError "Empty clauses."
         t:ts'
           | all (== t) ts' -> return t
           | otherwise ->
               throwError $ "Clauses do not all return the same type:\n"
                         ++ unlines (map show ts)



-- Type Checking

check :: Term -> Type -> TypeChecker ()
check (Lam sc) (Fun arg ret)
  = do i <- newName
       extendContext [(i,arg)]
         $ check (instantiate sc [Var (Generated i)]) ret
check (Lam sc) t
  = throwError $ "Cannot check term: " ++ show (Lam sc) ++ "\n"
              ++ "Against non-function type: " ++ show t
check m t
  = do t' <- infer m
       unless (t == t')
         $ throwError $ "Expected term: " ++ show m ++ "\n"
                     ++ "To have type: " ++ show t ++ "\n"
                     ++ "Instead found type: " ++ show t'



checkPattern :: Pattern -> Type -> TypeChecker Context
checkPattern (VarPat _) t
  = do i <- newName
       return [(i,t)]
checkPattern (ConPat c ps) t
  = do ConSig args ret <- typeInSignature c
       let lps = length ps
           largs = length args
       unless (lps == largs && t == ret)
         $ throwError $ c ++ " expects " ++ show largs ++ " "
                   ++ (if largs == 1 then "arg" else "args")
                   ++ " but was given " ++ show lps
       rss <- zipWithM checkPattern ps args
       return $ concat rss