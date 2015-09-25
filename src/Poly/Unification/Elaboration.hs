{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Poly.Unification.Elaboration where

import Control.Applicative ((<$>),(<*>))
import Control.Monad (when,unless)
import Control.Monad.Reader
import Control.Monad.State
import Data.List (intercalate)
import Data.Maybe (isJust)

import Abs
import Scope
import Poly.Core.Term
import Poly.Core.Type
import Poly.Core.Program

import Poly.Unification.TypeChecking hiding (signature,definitions,putDefinitions,context,putContext)


data ElabState
  = ElabState
    { elabSig :: Signature
    , elabDefs :: Definitions
    , elabCtx :: Context
    }

type Elaborator a = StateT ElabState (Either String) a

runElaborator :: Elaborator () -> Either String ElabState
runElaborator elab = do (_,p) <- runStateT elab (ElabState (Signature [] []) [] [])
                        return p

signature :: Elaborator Signature
signature = elabSig <$> get

definitions :: Elaborator Definitions
definitions = elabDefs <$> get

context :: Elaborator Context
context = elabCtx <$> get

putSignature :: Signature -> Elaborator ()
putSignature sig = do s <- get
                      put (s { elabSig = sig })

putDefinitions :: Definitions -> Elaborator ()
putDefinitions defs = do s <- get
                         put (s { elabDefs = defs })

putContext :: Context -> Elaborator ()
putContext ctx = do s <- get
                    put (s { elabCtx = ctx })

when' :: TypeChecker a -> Elaborator () -> Elaborator ()
when' tc e = do ElabState sig defs ctx <- get
                case runTypeChecker tc sig defs ctx of
                  Nothing -> return ()
                  Just _  -> e

unless' :: TypeChecker a -> Elaborator () -> Elaborator ()
unless' tc e = do ElabState sig defs ctx <- get
                  case runTypeChecker tc sig defs ctx of
                    Nothing -> e
                    Just _  -> return ()

addDeclaration :: String -> Term -> Type -> Elaborator ()
addDeclaration n def ty = do defs <- definitions
                             putDefinitions ((n,def,ty) : defs)

addTypeConstructor :: String -> Int -> Elaborator ()
addTypeConstructor n arity
  = do Signature tyconsigs consigs <- signature
       putSignature (Signature ((n,TyConSig arity):tyconsigs) consigs)

addConstructor :: String -> ConSig -> Elaborator ()
addConstructor n consig
  = do Signature tycons consigs <- signature
       putSignature (Signature tycons ((n,consig):consigs))



elabTermDecl :: TermDeclaration -> Elaborator ()
elabTermDecl (TermDeclaration n ty def)
  = do when' (typeInDefinitions n)
           $ fail ("Term already defined: " ++ n)
       unless' (isType ty)
             $ fail ("Invalid type: " ++ show ty)
       unless' (extendDefinitions [(n,def,ty)] (check def ty))
             $ fail ("Definition value does not type check." ++
                     "\n  Term: " ++ show def ++
                     "\n  Expected type: " ++ show ty)
       addDeclaration n def ty



instance Abstract String Type Type where
  abstract (TyVar (TyName x))
    = reader $ \e ->
        case lookup x e of
          Nothing -> TyVar (TyName x)
          Just m  -> m
  abstract (TyVar (TyGenerated i))
    = return $ TyVar (TyGenerated i)
  abstract (TyCon c as)
    = TyCon c <$> mapM abstract as
  abstract (Fun a b)
    = Fun <$> abstract a <*> abstract b
  abstract (Forall sc)
    = Forall <$> abstractScope sc

forallHelper :: String -> Type -> Type
forallHelper x b = Forall (Scope [x] $ \[a] -> runReader (abstract b) [(x,a)])

elabAlt :: String -> [String] -> String -> [Type] -> Elaborator ()
elabAlt tycon params n args
  = do when' (typeInSignature n)
           $ fail ("Constructor already declared: " ++ n)
       let args' = mapM abstract args
           ret' = abstract (TyCon tycon (map (TyVar . TyName) params))
           consig' = ConSig (length params) (Scope params $ \vs ->
                       let e = zip params vs
                       in (runReader args' e, runReader ret' e))
       unless' (sequence_ (map isType args))
             $ fail ("Invalid constructor signature: " ++
                     show consig')
       addConstructor n consig'
  
elabAlts :: String -> [String] -> [(String, [Type])] -> Elaborator ()
elabAlts tycon params [] = return ()
elabAlts tycon params ((n,args):cs) = do elabAlt tycon params n args
                                         elabAlts tycon params cs

elabTypeDecl :: TypeDeclaration -> Elaborator ()
elabTypeDecl (TypeDeclaration tycon params alts)
  = do when' (isType (TyCon tycon (map (TyVar . TyName) params)))
           $ fail ("Type constructor already declared: " ++ tycon)
       addTypeConstructor tycon (length params)
       elabAlts tycon params alts

elabProgram :: Program -> Elaborator ()
elabProgram (Program stmts) = go stmts
  where
    go :: [Statement] -> Elaborator ()
    go [] = return ()
    go (TyDecl td:stmts) = do elabTypeDecl td
                              go stmts
    go (TmDecl td:stmts) = do elabTermDecl td
                              go stmts