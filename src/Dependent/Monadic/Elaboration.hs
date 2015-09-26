module Dependent.Monadic.Elaboration where

import Control.Applicative ((<$>))
import Control.Monad (when,unless)
import Control.Monad.Reader
import Control.Monad.State
import Data.List (intercalate)
import Data.Maybe (isJust)

import Abs
import Scope
import Dependent.Core.Abstraction
import Dependent.Core.ConSig
import Dependent.Core.Program
import Dependent.Core.Term

import Dependent.Monadic.TypeChecking hiding (signature,definitions,context)



data ElabState
  = ElabState
    { elabSig :: Signature Term
    , elabDefs :: Definitions
    , elabCtx :: Context
    }

type Elaborator a = StateT ElabState (Either String) a

runElaborator :: Elaborator () -> Either String ElabState
runElaborator elab = do (_,p) <- runStateT elab (ElabState [] [] [])
                        return p

signature :: Elaborator (Signature Term)
signature = elabSig <$> get

context :: Elaborator Context
context = elabCtx <$> get

definitions :: Elaborator Definitions
definitions = elabDefs <$> get

putSignature :: Signature Term -> Elaborator ()
putSignature sig = do s <- get
                      put (s { elabSig = sig })

putContext :: Context -> Elaborator ()
putContext ctx = do s <- get
                    put (s { elabCtx = ctx})

putDefinitions :: Definitions -> Elaborator ()
putDefinitions defs = do s <- get
                         put (s {elabDefs = defs })

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


addDeclaration :: String -> Term -> Term -> Elaborator ()
addDeclaration n def ty = do defs <- definitions
                             putDefinitions ((n,def,ty) : defs)

addConstructor :: String -> ConSig Term -> Elaborator ()
addConstructor c consig
  = do sig <- signature
       putSignature ((c,consig):sig)




elabTermDecl :: TermDeclaration -> Elaborator ()
elabTermDecl (TermDeclaration n ty def)
  = do when' (typeInDefinitions n)
           $ fail ("Term already defined: " ++ n)
       unless' (check ty Type)
             $ fail ("Invalid type: " ++ show ty)
       unless' (extendDefinitions [(n,def,ty)] (check def ty))
             $ fail ("Definition value does not type check." ++
                     "\n  Term: " ++ show def ++
                     "\n  Expected type: " ++ show ty)
       addDeclaration n def ty



elabAlt :: String -> ConSig Term -> Elaborator ()
elabAlt c consig
  = do when' (typeInSignature c)
           $ fail ("Constructor already declared: " ++ c)
       unless' (checkConSig consig)
             $ fail ("Invalid constructor signature: " ++
                     c ++ " " ++ showConSig (Var . Name) consig)
       addConstructor c consig

elabTypeDecl :: TypeDeclaration -> Elaborator ()
elabTypeDecl (TypeDeclaration tycon tyconargs alts)
  = do let tyconSig = conSigHelper tyconargs Type
       when' (typeInSignature tycon)
           $ fail ("Type constructor already declared: " ++ tycon)
       unless' (checkConSig tyconSig)
             $ fail ("Type constructor does not type check: " ++
                     tycon ++ " " ++ showConSig (Var . Name) tyconSig)
       addConstructor tycon tyconSig
       mapM_ (uncurry elabAlt) alts



elabProgram :: Program -> Elaborator ()
elabProgram (Program stmts) = go stmts
  where
    go :: [Statement] -> Elaborator ()
    go [] = return ()
    go (TyDecl td:stmts) = do elabTypeDecl td
                              go stmts
    go (TmDecl td:stmts) = do elabTermDecl td
                              go stmts