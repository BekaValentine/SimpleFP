module Simple.Monadic.Elaboration where

import Control.Monad (when,unless)
import Control.Monad.Trans.State
import Data.List (intercalate)
import Data.Maybe (isJust)

import Simple.Core.Term
import Simple.Core.Type
import Simple.Core.Program

import Simple.Monadic.TypeChecking hiding (signature,definitions,context)


type Elaborator a = StateT (Signature,Definitions,Context) (Either String) a

runElaborator :: Elaborator () -> Either String (Signature,Definitions,Context)
runElaborator elab = do (_,p) <- runStateT elab (Signature [] [],[],[])
                        return p

signature :: Elaborator Signature
signature = do (sig,_,_) <- get
               return sig

context :: Elaborator Context
context = do (_,_,ctx) <- get
             return ctx

definitions :: Elaborator Definitions
definitions = do (_,defs,_) <- get
                 return defs

putSignature :: Signature -> Elaborator ()
putSignature sig = do (_,defs,ctx) <- get
                      put (sig,defs,ctx)

putContext :: Context -> Elaborator ()
putContext ctx = do (sig,defs,_) <- get
                    put (sig,defs,ctx)

putDefinitions :: Definitions -> Elaborator ()
putDefinitions defs = do (sig,_,ctx) <- get
                         put (sig,defs,ctx)

when' :: TypeChecker a -> Elaborator () -> Elaborator ()
when' tc e = do (sig,defs,ctx) <- get
                case runTypeChecker tc sig defs ctx of
                  Nothing -> return ()
                  Just _  -> e

unless' :: TypeChecker a -> Elaborator () -> Elaborator ()
unless' tc e = do (sig,defs,ctx) <- get
                  case runTypeChecker tc sig defs ctx of
                    Nothing -> e
                    Just _  -> return ()


addDeclaration :: String -> Term -> Type -> Elaborator ()
addDeclaration n def ty = do defs <- definitions
                             putDefinitions ((n,def,ty) : defs)

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