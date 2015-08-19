module PolyConstraint.Elaboration where

import Control.Monad (when,unless)
import Control.Monad.Trans.State
import Data.List (intercalate)
import Data.Maybe (isJust)

import Poly.Term
import Poly.Type
import Poly.Program

import PolyConstraint.TypeChecking hiding (signature,context,putContext)


type Elaborator a = StateT (Signature,Context) (Either String) a

runElaborator :: Elaborator () -> Either String (Signature,Context)
runElaborator elab = do (_,p) <- runStateT elab (Signature [] [],[])
                        return p

signature :: Elaborator Signature
signature = do (sig,_) <- get
               return sig

context :: Elaborator Context
context = do (_,ctx) <- get
             return ctx

putSignature :: Signature -> Elaborator ()
putSignature sig = do ctx <- context
                      put (sig,ctx)

putContext :: Context -> Elaborator ()
putContext ctx = do sig <- signature
                    put (sig,ctx)

when' :: TypeChecker a -> Elaborator () -> Elaborator ()
when' tc e = do (sig,ctx) <- get
                case runTypeChecker tc sig (contextToPatternContext ctx) of
                  Nothing -> return ()
                  Just _  -> e

unless' :: TypeChecker a -> Elaborator () -> Elaborator ()
unless' tc e = do (sig,ctx) <- get
                  case runTypeChecker tc sig (contextToPatternContext ctx) of
                    Nothing -> e
                    Just _  -> return ()

addDeclaration :: String -> Term -> Type -> Elaborator ()
addDeclaration n def ty = do ctx <- context
                             putContext (HasDef n def ty : ctx)

addTypeConstructor :: String -> Int -> Elaborator ()
addTypeConstructor n arity = do Signature tyconsigs consigs <- signature
                                putSignature (Signature ((n,TyConSig arity):tyconsigs) consigs)

addConstructor :: String -> [String] -> String -> [Type] -> Elaborator ()
addConstructor tycon params n args
  = do Signature tycons consigs <- signature
       let consig = ConSig params args (TyCon tycon (map TyVar params))
       putSignature (Signature tycons ((n,consig):consigs))




elabTermDecl :: TermDeclaration -> Elaborator ()
elabTermDecl (TermDeclaration n ty def)
  = do let ty' = typeToPatternType ty
       when' (typeInContext n)
           $ fail ("Term already defined: " ++ n)
       unless' (isType [] ty)
             $ fail ("Invalid type: " ++ show ty)
       unless' (extend [PHasType n ty'] (check def ty'))
             $ fail ("Definition value does not type check." ++
                     "\n  Term: " ++ show def ++
                     "\n  Expected type: " ++ show ty)
       addDeclaration n def ty



elabAlt :: String -> [String] -> String -> [Type] -> Elaborator ()
elabAlt tycon params n args
  = do when' (typeInSignature n)
           $ fail ("Constructor already declared: " ++ n)
       unless' (sequence_ (map (isType params) args))
             $ fail ("Invalid constructor signature: " ++
                     show (ConSig params args (TyCon tycon (map TyVar params))))
       addConstructor tycon params n args

elabAlts :: String -> [String] -> [(String, [Type])] -> Elaborator ()
elabAlts tycon params [] = return ()
elabAlts tycon params ((n,args):cs) = do elabAlt tycon params n args
                                         elabAlts tycon params cs

elabTypeDecl :: TypeDeclaration -> Elaborator ()
elabTypeDecl (TypeDeclaration tycon params alts)
  = do when' (isType [] (TyCon tycon (map TyVar params)))
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