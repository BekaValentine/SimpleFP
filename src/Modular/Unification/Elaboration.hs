{-# OPTIONS -Wall #-}

module Modular.Unification.Elaboration where

import Control.Applicative ((<$>))
import Control.Monad.Except
import Control.Monad.State
import Data.List (nub,(\\),intersect,sort,groupBy,partition)

import Plicity
import Scope
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
                putAliases ((Left n,(m,n)):(Right (m,n),(m,n)):als)

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

ensureOpenSettingsAreValid :: [OpenSettings] -> Elaborator ()
ensureOpenSettingsAreValid oss
  = forM_ oss $ \(OpenSettings m a hu r) -> do
      ensureModuleExists m
      openAsIsValid a
      hidingUsingIsValid m hu
      renamingIsValid m a hu r
       
  where
    ensureModuleExists :: String -> Elaborator ()
    ensureModuleExists m
      = do ms <- moduleNames
           unless (m `elem` ms)
             $ throwError $ "The module " ++ m ++ " is not a known module."
    
    openAsIsValid :: Maybe String -> Elaborator ()
    openAsIsValid Nothing = return ()
    openAsIsValid (Just m')
      = do ms <- moduleNames
           unless (not (m' `elem` ms))
             $ throwError $ "The module name " ++ m' ++ " is already in use."
    
    hidingUsingIsValid :: String -> Maybe HidingUsing -> Elaborator ()
    hidingUsingIsValid _ Nothing = return ()
    hidingUsingIsValid m (Just hu')
      = do defs <- definitions
           sig <- signature
           let ns = nub (case hu' of { Hiding ns' -> ns' ; Using ns' -> ns' })
               known = nub ([ n | ((_,n),_,_) <- defs ] ++ [ n | ((_,n),_) <- sig ])
               missing = ns \\ known
           unless (null missing)
             $ throwError $ "The module " ++ m ++ " does not declare these symbols: "
                         ++ unwords missing
    
    renamingIsValid :: String -> Maybe String -> Maybe HidingUsing -> [(String,String)] -> Elaborator ()
    renamingIsValid m a hu r
      = do defs <- definitions
           sig <- signature
           let ns = nub [ n | (n,_) <- r ]
               known = nub ([ n | ((m',n),_,_) <- defs, m' == m ] ++ [ n | ((m',n),_) <- sig, m' == m ])
               missing = ns \\ known
           unless (null missing)
             $ throwError $ "The module " ++ m ++ " does not declare these symbols: "
                         ++ unwords ns
           let knownBeingUsed = case hu of
                                  Nothing -> known
                                  Just (Using used) -> used
                                  Just (Hiding hidden) -> known \\ hidden
               missingUsed = ns \\ knownBeingUsed
           unless (null missingUsed)
             $ throwError $ "The following symbols are not being opened: " ++ unwords missingUsed
           let ns' = [ n' | (_,n') <- r ]
               preserved = known \\ ns
               overlappingNames = [ x | x:xs <- groupBy (==) (sort (ns' ++ preserved)), length xs /= 0 ]
           unless (null overlappingNames)
             $ throwError $ "These symbols will be overlapping when the module " ++ m
                         ++ " is opened: " ++ unwords overlappingNames
           als <- aliases
           let combine = case a of
                           Nothing -> Left
                           Just m' -> \n' -> Right (m',n')
               mns' = nub [ combine n' | (_,n') <- r ]
               knownAls = nub [ al | (al,_) <- als ]
               overlap = intersect mns' knownAls
               showLR (Left n0) = n0
               showLR (Right (m0,n0)) = m0 ++ "." ++ n0
           unless (null overlap)
             $ throwError $ "These symbols are already in scope: "
                         ++ unwords (map showLR overlap)
           
extendAliases :: [OpenSettings] -> Elaborator a -> Elaborator a
extendAliases settings tc
  = do ensureOpenSettingsAreValid settings
       als <- aliases
       sig <- signature
       defs <- definitions
       let newAls = newAliases sig defs settings ++ als
       putAliases newAls
       x <- tc
       putAliases als
       return x

newAliases :: Signature Term -> Definitions -> [OpenSettings] -> ModuleAliases
newAliases _ _ [] = []
newAliases sig defs (os:oss)
  = let als  = newAliasesFromSettings os
        als' = newAliases sig defs oss
    in als' ++ als
  where    
    newAliasesFromSettings :: OpenSettings -> ModuleAliases
    newAliasesFromSettings (OpenSettings m a hu r)
      = let openedSymbols = [ (m',c) | ((m',c),_) <- sig, m' == m ]
                         ++ [ (m',x) | ((m',x),_,_) <- defs, m' == m ]
            usedSymbols = used hu openedSymbols
            renamedSymbols = renamed r usedSymbols
            asedSymbols = ased a renamedSymbols
        in asedSymbols
    
    used :: Maybe HidingUsing -> [(String,String)] -> [(String,String)]
    used Nothing            = id
    used (Just (Hiding ns)) = filter (\(_,n) -> not (n `elem` ns))
    used (Just (Using ns))  = filter (\(_,n) -> (n `elem` ns))
    
    renamed :: [(String,String)] -> [(String,String)] -> [(String,(String,String))]
    renamed r mns = [ (maybe n id (lookup n r), (m,n)) | (m,n) <- mns ]
    
    ased :: Maybe String -> [(String,(String,String))] -> [(Either String (String,String), (String,String))]
    ased Nothing   ns = [ (Left x, (m,n)) | (x,(m,n)) <- ns ]
    ased (Just m') ns = [ (Right (m',x), (m,n)) | (x,(m,n)) <- ns ]


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
elabTermDecl (WhereDeclaration n ty preclauses)
  = case preclauses of
      [] -> throwError "Cannot create an empty let-where definition."
      [(plics,(ps,xs,b))] | all isVarPat ps
        -> elabTermDecl (TermDeclaration n ty (helperFold (uncurry lamHelper) (zip plics xs) b))
      (_,(ps0,_,_)):_
        -> do let lps0 = length ps0
              unless (all (\(_,(ps,_,_)) -> length ps == lps0) preclauses)
                $ throwError "Mismatching number of patterns in different clauses of a pattern matching function."
              let (plics:plicss) = map fst preclauses
              unless (all (plics==) plicss)
                $ throwError "Mismatching plicities in different clauses of a pattern matching function"
              case truePlicities plics ty of
                Nothing
                  -> throwError $ "Cannot build a case expression motive from the type " ++ show ty
                Just truePlics
                  -> do let mot = motiveAux (length truePlics) ty
                            clauses = [ clauseHelper (truePatterns truePlics ps) xs b | (_,(ps,xs,b)) <- preclauses ]
                            plicsForLambdaAux = map (either id id) truePlics
                        elabTermDecl (TermDeclaration n ty (lambdaAux (\as -> Case as mot clauses) plicsForLambdaAux))
  where
    isVarPat :: Pattern -> Bool
    isVarPat (VarPat _) = True
    isVarPat _ = False
    
    lambdaAux :: ([Term] -> Term) -> [Plicity] -> Term
    lambdaAux f [] = f []
    lambdaAux f (plic:plics) = Lam plic (Scope ["_" ++ show (length plics)] $ \[x] -> lambdaAux (f . (x:)) plics)
    
    truePlicities :: [Plicity] -> Term -> Maybe [Either Plicity Plicity]
    truePlicities [] _ = Just []
    truePlicities (Expl:plics) (Fun Expl _ sc)
      = do rest <- truePlicities plics (descope (Var . Name) sc)
           return $ Right Expl : rest
    truePlicities (Expl:plics) (Fun Impl _ sc)
      = do rest <- truePlicities (Expl : plics) (descope (Var . Name) sc)
           return $ Left Impl : rest
    truePlicities (Impl:_) (Fun Expl _ _)
      = Nothing
    truePlicities (Impl:plics) (Fun Impl _ sc)
      = do rest <- truePlicities plics (descope (Var . Name) sc)
           return $ Right Impl : rest
    
    motiveAux :: Int -> Term -> CaseMotive
    motiveAux 0 t = CaseMotiveNil t
    motiveAux i (Fun _ a (Scope ns b)) = CaseMotiveCons a (Scope ns (motiveAux (i-1) . b))
    
    truePatterns :: [Either Plicity Plicity] -> [Pattern] -> [Pattern]
    truePatterns [] [] = []
    truePatterns (Right _:plics) (p:ps)
      = p : truePatterns plics ps
    truePatterns (Left _:plics) ps
      = MakeMeta : truePatterns plics ps



elabAlt :: String -> String -> ConSig Term -> Elaborator ()
elabAlt tycon c consig
  = do validConSig consig
       when' (typeInSignature (BareCon c))
           $ throwError ("Constructor already declared: " ++ c)
       addAlias c
       consig' <- liftTC (checkifyConSig consig)
       addConstructor c consig'
  where
    validConSig :: ConSig Term -> Elaborator ()
    validConSig (ConSigNil (Con (BareCon tc) _))
      = unless (tc == tycon)
          $ throwError $ "The constructor " ++ c ++ " should constructor a value of the type " ++ tycon
                      ++ " but instead produces a " ++ tc
    validConSig (ConSigNil a)
      = throwError $ "The constructor " ++ c ++ " should constructor a value of the type " ++ tycon
                  ++ " but instead produces " ++ show a
    validConSig (ConSigCons _ _ sc)
      = validConSig (descope (Var . Name) sc)

elabTypeDecl :: TypeDeclaration -> Elaborator ()
elabTypeDecl (TypeDeclaration tycon tyconargs alts)
  = do let tyconSig = conSigHelper tyconargs Type
       when' (typeInSignature (BareCon tycon))
           $ throwError ("Type constructor already declared: " ++ tycon)
       addAlias tycon
       tyconSig' <- liftTC (checkifyConSig tyconSig)
       addConstructor tycon tyconSig'
       mapM_ (uncurry (elabAlt tycon)) alts

elabModule :: Module -> Elaborator ()
elabModule (Module m settings stmts0)
  = do addModuleName m
       putModuleName m
       ensureOpenSettingsAreValid settings
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


sortModules :: [Module] -> Elaborator [Module]
sortModules mods = go [] mods
  where
    splitModules :: [String] -> [Module] -> Elaborator ([Module], [Module])
    splitModules prev mods
      = let (next,rest) = partition (\(Module _ settings _) -> all (\s -> openModule s `elem` prev) settings) mods
        in if null next
           then throwError $ "The following modules have circular dependencies which prevent resolution: "
                          ++ unwords [ n | Module n _ _ <- rest ]
           else return (next,rest)
    
    go :: [String] -> [Module] -> Elaborator [Module]
    go _ []
      = return []
    go prev mods
      = do (next,rest) <- splitModules prev mods
           let newPrev = [ n | Module n _ _ <- next ]
           rest' <- go (newPrev ++ prev) rest
           return (next ++ rest')

elabProgram :: Program -> Elaborator ()
elabProgram (Program mods)
  = do sortedMods <- sortModules mods
       mapM_ elabModule sortedMods