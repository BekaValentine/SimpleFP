{-# OPTIONS -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module TypeChecker where

import Control.Monad.State

class TypeCheckerState s where
  type Sig s
  type Defs s
  type Ctx s
  typeCheckerSig :: s -> Sig s
  putTypeCheckerSig :: s -> Sig s -> s
  typeCheckerDefs :: s -> Defs s
  putTypeCheckerDefs :: s -> Defs s -> s
  addTypeCheckerDefs :: s -> Defs s -> s
  typeCheckerCtx :: s -> Ctx s
  putTypeCheckerCtx :: s -> Ctx s -> s
  addTypeCheckerCtx :: s -> Ctx s -> s
  typeCheckerNextName :: s -> Int
  putTypeCheckerNextName :: s -> Int -> s



type MonadTC s m = (TypeCheckerState s, Functor m, MonadState s m)

signature :: MonadTC s m => m (Sig s)
signature = fmap typeCheckerSig get

putSignature :: MonadTC s m => Sig s -> m ()
putSignature sig
  = do s <- get
       put (putTypeCheckerSig s sig)

definitions :: MonadTC s m => m (Defs s)
definitions = fmap typeCheckerDefs get

putDefinitions :: MonadTC s m => Defs s -> m ()
putDefinitions defs
  = do s <- get
       put (putTypeCheckerDefs s defs)

extendDefinitions :: MonadTC s m => Defs s -> m a -> m a
extendDefinitions edefs tc
  = do s <- get
       put (addTypeCheckerDefs s edefs)
       x <- tc
       putDefinitions (typeCheckerDefs s)
       return x

context :: MonadTC s m => m (Ctx s)
context = fmap typeCheckerCtx get

putContext :: MonadTC s m => Ctx s -> m ()
putContext ctx
  = do s <- get
       put (putTypeCheckerCtx s ctx)

extendContext :: MonadTC s m => Ctx s -> m a -> m a
extendContext ectx tc
  = do s <- get
       put (addTypeCheckerCtx s ectx)
       x <- tc
       putContext (typeCheckerCtx s)
       return x

newName :: MonadTC s m => m Int
newName = do s <- get
             let n = typeCheckerNextName s
             put (putTypeCheckerNextName s (n+1))
             return $ n



class TypeCheckerMetas s where
  type Subs s
  typeCheckerNextMeta :: s -> Int
  putTypeCheckerNextMeta :: s -> Int -> s
  typeCheckerSubs :: s -> Subs s
  putTypeCheckerSubs :: s -> Subs s -> s

type MonadPolyTC s m = (TypeCheckerMetas s, MonadTC s m)

newMetaVar :: MonadPolyTC s m => m Int
newMetaVar = do s <- get
                let n = typeCheckerNextMeta s
                put (putTypeCheckerNextMeta s (n+1))
                return n

substitution :: MonadPolyTC s m => m (Subs s)
substitution = fmap typeCheckerSubs get

putSubstitution :: MonadPolyTC s m => Subs s -> m ()
putSubstitution subs = do s <- get
                          put (putTypeCheckerSubs s subs)