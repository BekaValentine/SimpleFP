{-# OPTIONS -Wall #-}

module Simple.Unification.Elaboration where

import Control.Applicative ((<$>))
import Control.Monad.Except
import Control.Monad.State

import Scope
import TypeChecker (extendDefinitions)

import Simple.Core.Abstraction
import Simple.Core.Term
import Simple.Core.Type
import Simple.Core.Program

import Simple.Unification.TypeChecking


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



elabAlt :: String -> String -> [Type] -> Elaborator ()
elabAlt tycon n args
  = do when' (typeInSignature n)
           $ throwError ("Constructor already declared: " ++ n)
       liftTC (mapM_ isType args)
       addConstructor tycon n args

elabAlts :: String -> [(String, [Type])] -> Elaborator ()
elabAlts _     [] = return ()
elabAlts tycon ((n,args):cs) = do elabAlt tycon n args
                                  elabAlts tycon cs

elabTypeDecl :: TypeDeclaration -> Elaborator ()
elabTypeDecl (TypeDeclaration tycon alts)
  = do when' (isType (TyCon tycon))
           $ throwError ("Type constructor already declared: " ++ tycon)
       addTypeConstructor tycon
       elabAlts tycon alts

elabProgram :: Program -> Elaborator ()
elabProgram (Program stmts0) = go stmts0
  where
    go :: [Statement] -> Elaborator ()
    go [] = return ()
    go (TyDecl td:stmts) = do elabTypeDecl td
                              go stmts
    go (TmDecl td:stmts) = do elabTermDecl td
                              go stmts