module Basic.Elaboration where

import Control.Monad (when,unless)
import Data.List (intercalate)
import Data.Maybe (isJust)

import Core.Term
import Core.Type
import Core.Programs

import Basic.TypeChecking


elabTermDecl :: Signature -> Context -> TermDeclaration -> Either String Context
elabTermDecl sig ctx (TermDeclaration n ty def)
  = do when (Nothing /= typeInContext n ctx)
          $ Left ("String already defined: " ++ n)
       unless (isType sig ty)
            $ Left ("Invalid type: " ++ show ty)
       unless (check sig (HasType n ty:ctx) def ty)
            $ Left ("Definition value does not type check." ++
                    "\n  Term: " ++ show def ++
                    "\n  Expected type: " ++ show ty)
       return $ HasDef n def ty : ctx


elabAlt :: Signature -> String -> String -> [Type] -> Either String Signature
elabAlt sig@(Signature tycons consigs) tycon n args
  = do when (isJust (typeInSignature n sig))
          $ Left ("Constructor already declared: " ++ n)
       unless (all (isType (Signature (tycon:tycons) consigs)) args)
            $ Left ("Invalid constructor signature: " ++ show (ConSig args (TyCon tycon)))
       return $ Signature tycons ((n,ConSig args (TyCon tycon)):consigs)


elabAlts :: Signature -> String -> [(String, [Type])] -> Either String Signature
elabAlts sig tycon [] = return sig
elabAlts sig tycon ((n,args):cs)
  = do sig' <- elabAlt sig tycon n args
       elabAlts sig' tycon cs


elabTypeDecl :: Signature -> Context -> TypeDeclaration -> Either String Signature
elabTypeDecl sig@(Signature tycons consigs) ctx (TypeDeclaration tycon alts)
  = do when (tycon `elem` tycons)
          $ Left ("Type constructor already declared: " ++ tycon)
       Signature tycons' consigs' <- elabAlts sig tycon alts
       return $ Signature (tycon:tycons') consigs'


elabProgram :: Program -> Either String (Signature, Context)
elabProgram (Program stmts) = go (Signature [] []) [] stmts
  where
    go sig ctx [] = return (sig,ctx)
    go sig ctx (TyDecl td:stmts)
      = do sig' <- elabTypeDecl sig ctx td
           go sig' ctx stmts
    go sig ctx (TmDecl td:stmts)
      = do ctx' <- elabTermDecl sig ctx td
           go sig ctx' stmts