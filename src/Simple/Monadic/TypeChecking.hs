{-# LANGUAGE RecursiveDo #-}

module Simple.Monadic.TypeChecking where

import Control.Applicative ((<$>))
import Control.Monad (guard)
import Control.Monad.State
import Data.List (intercalate,nub,find)

import Env
import Eval
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

type TypeChecker a = StateT TCState Maybe a

runTypeChecker :: TypeChecker a -> Signature -> Definitions -> Context -> Maybe a
runTypeChecker tc sig defs ctx
  = fmap fst (runStateT tc (TCState sig defs ctx 0))

failure :: TypeChecker a
failure = StateT $ \_ -> Nothing

signature :: TypeChecker Signature
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

tyconExists :: String -> TypeChecker ()
tyconExists n = do Signature tycons _ <- signature
                   guard $ n `elem` tycons

typeInSignature :: String -> TypeChecker ConSig
typeInSignature n = do Signature _ consigs <- signature
                       case lookup n consigs of
                         Nothing -> failure
                         Just t  -> return t

typeInDefinitions :: String -> TypeChecker Type
typeInDefinitions x
  = do defs <- definitions
       case find (\(y,_,_) -> y == x) defs of
         Nothing      -> failure
         Just (_,_,t) -> return t

typeInContext :: Int -> TypeChecker Type
typeInContext i
  = do ctx <- context
       case lookup i ctx of
         Nothing -> failure
         Just t  -> return t



-- Type well-formedness

isType :: Type -> TypeChecker ()
isType (TyCon tc) = tyconExists tc
isType (Fun a b)  = isType a >> isType b



-- Type Inference

infer :: Term -> TypeChecker Type
infer (Var (Name x))
  = typeInDefinitions x
infer (Var (Generated i))
  = typeInContext i
infer (Ann m t)
  = check m t >> return t
infer (Lam sc)
  = failure
infer (App f a)
  = do Fun arg ret <- infer f
       check a arg
       return ret
infer (Con c as)
  = do ConSig args ret <- typeInSignature c
       guard $ length as == length args
       sequence_ (zipWith check as args)
       return ret
infer (Case m cs)
  = do t <- infer m
       inferClauses t cs


inferClause :: Type -> Clause -> TypeChecker Type
inferClause patTy (Clause p sc)
  = do ctx' <- checkPattern p patTy
       let xs = [ Var (Generated i) | (i,_) <- ctx' ]
       ctx <- context
       extendContext ctx'
         $ infer (instantiate sc xs)

inferClauses :: Type -> [Clause] -> TypeChecker Type
inferClauses patTy cs = do ts <- sequence $ map (inferClause patTy) cs
                           case ts of
                             t:ts | all (== t) ts
                               -> return t
                             _ -> failure



-- Type Checking

check :: Term -> Type -> TypeChecker ()
check (Var x) t
  = do t' <- infer (Var x)
       guard $ t == t'
check (Ann m t') t
  = do guard $ t == t'
       check m t'
check (Lam sc) (Fun arg ret)
  = do i <- newName
       extendContext [(i,arg)]
         $ check (instantiate sc [Var (Generated i)]) ret
check (App f a) t
  = do t' <- infer (App f a)
       guard $ t == t'
check (Con c as) t
 = do t' <- infer (Con c as)
      guard $ t == t'
check (Case m cs) t
  = do t' <- infer (Case m cs)
       guard $ t == t'
check _ _
  = failure



checkPattern :: Pattern -> Type -> TypeChecker Context
checkPattern VarPat t
  = do i <- newName
       return [(i,t)]
checkPattern (ConPat c ps) t
  = do ConSig args ret <- typeInSignature c
       guard $ length ps == length args
            && t == ret
       rss <- zipWithM checkPattern ps args
       return $ concat rss