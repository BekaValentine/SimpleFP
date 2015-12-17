{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Poly.Unification.Elaboration where

import Control.Applicative ((<$>),(<*>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Abs
import Scope
import TypeChecker (extendDefinitions)

import Poly.Core.Abstraction
import Poly.Core.Term
import Poly.Core.Type
import Poly.Core.Program

import Poly.Unification.TypeChecking


data ElabState
  = ElabState
    { elabSig :: Signature
    , elabDefs :: Definitions
    , elabCtx :: Context
    , elabNextName :: Int
    }

type Elaborator a = StateT ElabState (Either String) a

runElaborator :: Elaborator () -> Either String ElabState
runElaborator elab = do (_,p) <- runStateT elab (ElabState (Signature [] []) [] [] 0)
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
when' tc e = do ElabState sig defs ctx i <- get
                case runTypeChecker tc sig defs ctx i of
                  Left _   -> return ()
                  Right _  -> e

liftTC :: TypeChecker a -> Elaborator a
liftTC tc = do ElabState sig defs ctx i <- get
               case runTypeChecker tc sig defs ctx i of
                 Left e  -> throwError e
                 Right (a,s) -> do s' <- get
                                   put s' { elabNextName = tcNextName s }
                                   return a

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
           $ throwError ("Term already defined: " ++ n)
       liftTC (isType ty)
       liftTC (extendDefinitions [(n,def,ty)] (check def ty))
       addDeclaration n def ty
elabTermDecl (WhereDeclaration n ty preclauses)
  = case preclauses of
      [] -> throwError "Cannot create an empty let-where definition."
      [(ps,xs,b)] | all isVarPat ps
        -> elabTermDecl (TermDeclaration n ty (helperFold lamHelper xs b))
      (ps0,_,_):_
        -> let clauses = [ clauseHelper ps xs b | (ps,xs,b) <- preclauses ]
           in elabTermDecl (TermDeclaration n ty (lambdaAux (\as -> Case as clauses) (length ps0)))
   where
    isVarPat :: Pattern -> Bool
    isVarPat (VarPat _) = True
    isVarPat _ = False
    
    lambdaAux :: ([Term] -> Term) -> Int -> Term
    lambdaAux f 0 = f []
    lambdaAux f i = Lam (Scope ["_" ++ show i] $ \[x] -> lambdaAux (f . (x:)) (i-1))



forallHelper :: String -> Type -> Type
forallHelper x b = Forall (scope [x] b)

elabAlt :: String -> [String] -> String -> [Type] -> Elaborator ()
elabAlt tycon params n args
  = do when' (typeInSignature n)
           $ throwError ("Constructor already declared: " ++ n)
       let args' = mapM abstract args
           ret' = abstract (TyCon tycon (map (TyVar . TyName) params))
           consig' = ConSig (length params) (Scope params $ \vs ->
                       let e = zip params vs
                       in (runReader args' e, runReader ret' e))
       liftTC (mapM_ isType args)
       addConstructor n consig'
  
elabAlts :: String -> [String] -> [(String, [Type])] -> Elaborator ()
elabAlts _     _      [] = return ()
elabAlts tycon params ((n,args):cs) = do elabAlt tycon params n args
                                         elabAlts tycon params cs

elabTypeDecl :: TypeDeclaration -> Elaborator ()
elabTypeDecl (TypeDeclaration tycon params alts)
  = do when' (isType (TyCon tycon (map (TyVar . TyName) params)))
           $ throwError ("Type constructor already declared: " ++ tycon)
       addTypeConstructor tycon (length params)
       elabAlts tycon params alts

elabProgram :: Program -> Elaborator ()
elabProgram (Program stmts0) = go stmts0
  where
    go :: [Statement] -> Elaborator ()
    go [] = return ()
    go (TyDecl td:stmts) = do elabTypeDecl td
                              go stmts
    go (TmDecl td:stmts) = do elabTermDecl td
                              go stmts