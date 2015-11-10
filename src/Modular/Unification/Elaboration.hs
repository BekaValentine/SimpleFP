{-# OPTIONS -Wall #-}

module Modular.Unification.Elaboration where

import Control.Applicative ((<$>))
import Control.Monad.Except
import Control.Monad.State

import TypeChecker (extendDefinitions)
import Modular.Core.Abstraction
import Modular.Core.ConSig
import Modular.Core.Program
import Modular.Core.Term
import Modular.Unification.TypeChecking hiding (aliases,putAliases,moduleNames)



data ElabState
  = ElabState
    { elabSig :: Signature Term
    , elabDefs :: Definitions
    , elabCtx :: Context
    , elabNextName :: Int
    , elabAliases :: ModuleAliases
    , elabModName :: String
    , elabModuleNames :: [String]
    }

type Elaborator a = StateT ElabState (Either String) a

runElaborator :: Elaborator () -> Either String ElabState
runElaborator elab = do (_,p) <- runStateT elab (ElabState [] [] [] 0 [] "" [])
                        return p

signature :: Elaborator (Signature Term)
signature = elabSig <$> get

context :: Elaborator Context
context = elabCtx <$> get

definitions :: Elaborator Definitions
definitions = elabDefs <$> get

aliases :: Elaborator ModuleAliases
aliases = elabAliases <$> get

moduleName :: Elaborator String
moduleName = elabModName <$> get

putSignature :: Signature Term -> Elaborator ()
putSignature sig = do s <- get
                      put (s { elabSig = sig })

putContext :: Context -> Elaborator ()
putContext ctx = do s <- get
                    put (s { elabCtx = ctx})

putDefinitions :: Definitions -> Elaborator ()
putDefinitions defs = do s <- get
                         put (s {elabDefs = defs })

putAliases :: ModuleAliases -> Elaborator ()
putAliases als = do s <- get
                    put (s { elabAliases = als })

addAlias :: String -> Elaborator ()
addAlias n = do als <- aliases
                m <- moduleName
                putAliases ((Left n,(m,n)):als)

putModuleName :: String -> Elaborator ()
putModuleName m = do s <- get
                     put (s { elabModName = m })

moduleNames :: Elaborator [String]
moduleNames = elabModuleNames <$> get

putModuleNames :: [String] -> Elaborator ()
putModuleNames ms = do s <- get
                       put (s { elabModuleNames = ms })

addModuleName :: String -> Elaborator ()
addModuleName m
  = do ms <- moduleNames
       unless (not (m `elem` ms))
         $ throwError $ "A module is already declared with the name " ++ m
       putModuleNames (m:ms)

when' :: TypeChecker a -> Elaborator () -> Elaborator ()
when' tc e = do ElabState sig defs ctx i als _ ms <- get
                case runTypeChecker tc sig defs ctx i als ms of
                  Left _  -> return ()
                  Right _ -> e

liftTC :: TypeChecker a -> Elaborator a
liftTC tc = do ElabState sig defs ctx i als _ ms <- get
               case runTypeChecker tc sig defs ctx i als ms of
                 Left e  -> throwError e
                 Right (a,s) -> do s' <- get
                                   put s' { elabNextName = tcNextName s }
                                   return a


addDeclaration :: String -> Term -> Term -> Elaborator ()
addDeclaration n def ty = do defs <- definitions
                             m <- moduleName
                             putDefinitions (((m,n),def,ty) : defs)

addConstructor :: String -> ConSig Term -> Elaborator ()
addConstructor c consig
  = do sig <- signature
       m <- moduleName
       putSignature (((m,c),consig):sig)



elabTermDecl :: TermDeclaration -> Elaborator ()
elabTermDecl (TermDeclaration n ty def)
  = do when' (typeInDefinitions n)
           $ throwError ("Term already defined: " ++ n)
       ty' <- liftTC (check ty Type)
       m <- moduleName
       addAlias n
       def' <- liftTC (extendDefinitions [((m,n),def,ty')] (check def ty'))
       addDeclaration n def' ty'



elabAlt :: String -> ConSig Term -> Elaborator ()
elabAlt c consig
  = do when' (typeInSignature (BareCon c))
           $ throwError ("Constructor already declared: " ++ c)
       addAlias c
       consig' <- liftTC (checkifyConSig consig)
       addConstructor c consig'

elabTypeDecl :: TypeDeclaration -> Elaborator ()
elabTypeDecl (TypeDeclaration tycon tyconargs alts)
  = do let tyconSig = conSigHelper tyconargs Type
       when' (typeInSignature (BareCon tycon))
           $ throwError ("Type constructor already declared: " ++ tycon)
       addAlias tycon
       tyconSig' <- liftTC (checkifyConSig tyconSig)
       addConstructor tycon tyconSig'
       mapM_ (uncurry elabAlt) alts

elabModule :: Module -> Elaborator ()
elabModule (Module m settings stmts0)
  = do addModuleName m
       putModuleName m
       liftTC (ensureOpenSettingsAreValid settings)
       als <- aliases
       sig <- signature
       defs <- definitions
       let newAls = newAliases sig defs settings ++ als
       putAliases newAls
       go stmts0
       putAliases als
  where
    go :: [Statement] -> Elaborator ()
    go [] = return ()
    go (TyDecl td:stmts) = do elabTypeDecl td
                              go stmts
    go (TmDecl td:stmts) = do elabTermDecl td
                              go stmts


elabProgram :: Program -> Elaborator ()
elabProgram (Program mods) = mapM_ elabModule mods