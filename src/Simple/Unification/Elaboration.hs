module Simple.Unification.Elaboration where

import Control.Applicative ((<$>))
import Control.Monad (when,unless)
import Control.Monad.State
import Data.List (intercalate)
import Data.Maybe (isJust)

import Simple.Core.Term
import Simple.Core.Type
import Simple.Core.Program

import Simple.Unification.TypeChecking hiding (signature,definitions,putDefinitions,context,putContext)


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
context = do elabCtx <$> get

putSignature :: Signature -> Elaborator ()
putSignature sig = do s <- get
                      put (s { elabSig = sig})

putDefinitions :: Definitions -> Elaborator ()
putDefinitions defs = do s <- get
                         put (s { elabDefs = defs})

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
                             putDefinitions ((n,def,ty):defs)

addTypeConstructor :: String -> Elaborator ()
addTypeConstructor n = do Signature tycons consigs <- signature
                          putSignature (Signature (n:tycons) consigs)

addConstructor :: String -> String -> [Type] -> Elaborator ()
addConstructor tycon n args
  = do Signature tycons consigs <- signature
       let consig = ConSig args (TyCon tycon)
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



elabAlt :: String -> String -> [Type] -> Elaborator ()
elabAlt tycon n args
  = do when' (typeInSignature n)
           $ fail ("Constructor already declared: " ++ n)
       unless' (sequence_ (map isType args))
             $ fail ("Invalid constructor signature: " ++
                     show (ConSig args (TyCon tycon)))
       addConstructor tycon n args

elabAlts :: String -> [(String, [Type])] -> Elaborator ()
elabAlts tycon [] = return ()
elabAlts tycon ((n,args):cs) = do elabAlt tycon n args
                                  elabAlts tycon cs

elabTypeDecl :: TypeDeclaration -> Elaborator ()
elabTypeDecl (TypeDeclaration tycon alts)
  = do when' (isType (TyCon tycon))
           $ fail ("Type constructor already declared: " ++ tycon)
       addTypeConstructor tycon
       elabAlts tycon alts

elabProgram :: Program -> Elaborator ()
elabProgram (Program stmts) = go stmts
  where
    go :: [Statement] -> Elaborator ()
    go [] = return ()
    go (TyDecl td:stmts) = do elabTypeDecl td
                              go stmts
    go (TmDecl td:stmts) = do elabTermDecl td
                              go stmts