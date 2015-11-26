{-# OPTIONS -Wall #-}
{-# LANGUAGE TypeFamilies #-}

module Record.Unification.TypeChecking where

import Control.Applicative ((<$>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List (nubBy,find,nub,(\\),intersect,sort,groupBy)

import Abs
import Eval
import Plicity
import Scope
import TypeChecker
import Record.Core.Abstraction ()
import Record.Core.ConSig
import Record.Core.Evaluation ()
import Record.Core.Term





extract :: (a -> Bool) -> [a] -> Maybe (a,[a])
extract _ [] = Nothing
extract p (x:xs)
  | p x       = Just (x,xs)
  | otherwise = do (y,xs') <- extract p xs
                   return (y,x:xs')




-- Definitions

type Definitions = [((String,String),Term,Term)]




-- Contexts

type Context = [(Int,Term)]




-- Unifying Type Checkers

data Equation = Equation Term Term

type MetaVar = Int

type Substitution = [(MetaVar,Term)]

type ModuleAliases = [(Either String (String,String), (String,String))]

data TCState
  = TCState
    { tcSig :: Signature Term
    , tcDefs :: Definitions
    , tcCtx :: Context
    , tcNextName :: Int
    , tcNextMeta :: MetaVar
    , tcSubs :: Substitution
    , tcAliases :: ModuleAliases
    , tcModuleNames :: [String]
    }

instance TypeCheckerState TCState where
  type Sig TCState = Signature Term
  type Defs TCState = Definitions
  type Ctx TCState = Context
  typeCheckerSig = tcSig
  putTypeCheckerSig s sig = s { tcSig = sig }
  typeCheckerDefs = tcDefs
  putTypeCheckerDefs s defs = s { tcDefs = defs }
  addTypeCheckerDefs s edefs = s { tcDefs = edefs ++ tcDefs s }
  typeCheckerCtx = tcCtx
  putTypeCheckerCtx s ctx = s { tcCtx = ctx }
  addTypeCheckerCtx s ectx = s { tcCtx = ectx ++ tcCtx s }
  typeCheckerNextName = tcNextName
  putTypeCheckerNextName s n = s { tcNextName = n }

instance TypeCheckerMetas TCState where
  type Subs TCState = Substitution
  typeCheckerNextMeta = tcNextMeta
  putTypeCheckerNextMeta s n = s { tcNextMeta = n }
  typeCheckerSubs = tcSubs
  putTypeCheckerSubs s subs = s { tcSubs = subs }

type TypeChecker a = StateT TCState (Either String) a

runTypeChecker :: TypeChecker a -> Signature Term -> Definitions -> Context -> Int -> ModuleAliases -> [String] -> Either String (a,TCState)
runTypeChecker checker sig defs ctx i als mods
  = runStateT checker (TCState sig defs ctx i 0 [] als mods)

aliases :: TypeChecker ModuleAliases
aliases = fmap tcAliases get

putAliases :: ModuleAliases -> TypeChecker ()
putAliases als = do s <- get
                    put s { tcAliases = als }

moduleNames :: TypeChecker [String]
moduleNames = fmap tcModuleNames get

occurs :: MetaVar -> Term -> Bool
occurs x (Meta y)         = x == y
occurs _ (Var _)          = False
occurs _ (DottedVar _ _)  = False
occurs x (Ann m t)        = occurs x m || occurs x t
occurs _ Type             = False
occurs x (Fun _ a sc)     = occurs x a || occurs x (descope (Var . Name) sc)
occurs x (Lam _ sc)       = occurs x (descope (Var . Name) sc)
occurs x (App _ f a)      = occurs x f || occurs x a
occurs x (Con _ as)       = any (occurs x . snd) as
occurs x (Case as mot cs) = any (occurs x) as || occursCaseMotive mot || any occursClause cs
  where
    occursCaseMotive (CaseMotiveNil m) = occurs x m
    occursCaseMotive (CaseMotiveCons a sc)
      = occurs x a || occursCaseMotive (descope (Var . Name) sc)
    
    occursClause (Clause psc sc) = any occursPattern (descope Name psc) || occurs x (descope (Var . Name) sc)
    
    occursPattern (VarPat _) = False
    occursPattern (ConPat _ xs) = any (occursPattern . snd) xs
    occursPattern (AssertionPat m) = occurs x m
occurs x (OpenIn _ m)       = occurs x m
occurs x (RecordType tele)  = occursTelescope tele
  where
    occursTelescope TelescopeNil = False
    occursTelescope (TelescopeCons _ t sc) = occurs x t || occursTelescope (descope (Var . Name) sc)
occurs x (RecordCon fields) = any (occurs x . snd) fields
occurs x (RecordDot m _)    = occurs x m

solve :: [Equation] -> TypeChecker Substitution
solve eqs0 = go eqs0 []
  where
    evalWithSubs :: Substitution -> Equation -> TypeChecker Equation
    evalWithSubs subs (Equation l r)
      = do l' <- evaluate (instantiateMetas subs l)
           r' <- evaluate (instantiateMetas subs r)
           return (Equation l' r')
    
    go [] subs' = return subs'
    go (Equation (Meta x) t2 : eqs) subs'
      = do unless (not (occurs x t2))
             $ throwError $ "Cannot unify because " ++ show (Meta x)
                         ++ " occurs in " ++ show t2
           eqs' <- mapM (evalWithSubs ((x,t2):subs')) eqs
           go eqs' ((x,t2):subs')
    go (Equation t1 (Meta y) : eqs) subs'
      = do unless (not (occurs y t1))
             $ throwError $ "Cannot unify because " ++ show (Meta y)
                         ++ " occurs in " ++ show t1
           eqs' <- mapM (evalWithSubs ((y,t1):subs')) eqs
           go eqs' ((y,t1):subs')
    go (Equation (Var x) (Var y) : eqs) subs'
      = do unless (x == y)
             $ throwError $ "Cannot unify variables " ++ show (Var x)
            ++ " and " ++ show (Var y)
           go eqs subs'
    go (Equation (DottedVar m1 x1) (DottedVar m2 x2):eqs) subs'
      = do unless (m1 == m2 && x1 == x2)
             $ throwError $ "Cannot unify symbols " ++ show (DottedVar m1 x1)
            ++ " and " ++ show (DottedVar m2 x2)
           go eqs subs'
    go (Equation (Ann m1 t1) (Ann m2 t2) : eqs) subs'
      = go (Equation m1 m2 : Equation t1 t2 : eqs) subs'
    go (Equation Type Type : eqs) subs'
      = go eqs subs'
    go (Equation (Fun plic1 a1 sc1) (Fun plic2 a2 sc2) : eqs) subs'
      = do unless (plic1 == plic2)
             $ throwError $ "Mismatched plicities when trying to unify "
                         ++ show (Fun plic1 a1 sc1) ++ " with "
                         ++ show (Fun plic2 a2 sc2)
           i <- newName
           let b1 = instantiate sc1 [Var (Generated i)]
               b2 = instantiate sc2 [Var (Generated i)]
           go (Equation a1 a2 : Equation b1 b2 : eqs) subs'
    go (Equation (Lam plic1 sc1) (Lam plic2 sc2) : eqs) subs'
      = do unless (plic1 == plic2)
             $ throwError $ "Mismatched plicities when trying to unify "
                         ++ show (Lam plic1 sc1) ++ " with "
                         ++ show (Lam plic2 sc2)
           i <- newName
           let b1 = instantiate sc1 [Var (Generated i)]
               b2 = instantiate sc2 [Var (Generated i)]
           go (Equation b1 b2 : eqs) subs'
    go (Equation (App plic1 f1 a1) (App plic2 f2 a2) : eqs) subs'
      = do unless (plic1 == plic2)
             $ throwError $ "Mismatched plicities when trying to unify "
                         ++ show (App plic1 f1 a1) ++ " with "
                         ++ show (App plic2 f2 a2)
           go (Equation f1 f2 : Equation a1 a2 : eqs) subs'
    go (Equation (Con c1 as1) (Con c2 as2) : eqs) subs'
      = do unless (c1 == c2)
             $ throwError $ "Mismatching constructors " ++ show c1 ++ " and " ++ show c2
           unless (length as1 == length as2)
             $ throwError $ "Mismatching number of arguments in "
                         ++ show (Con c1 as1) ++ " and "
                         ++ show (Con c2 as2)
           eqs' <- zipConArgs as1 as2
           go (eqs' ++ eqs) subs'
      where
        zipConArgs :: [(Plicity,Term)] -> [(Plicity,Term)] -> TypeChecker [Equation]
        zipConArgs [] [] = return []
        zipConArgs ((plic1',a1'):as1') ((plic2',a2'):as2')
          = if plic1' == plic2'
            then do
              eqs' <- zipConArgs as1' as2'
              return (Equation a1' a2':eqs')
            else
              throwError "Mismatching plicity."
        zipConArgs _ _
          = throwError "Mismatching number of arguments."
    go (Equation (Case as1 mot1 cs1) (Case as2 mot2 cs2) : eqs) subs'
      = do unless(length as1 == length as2)
             $ throwError $ "Mismatching number of case arguments in "
                         ++ show (Case as1 mot1 cs1) ++ " and "
                         ++ show (Case as2 mot2 cs2)
           unless (length cs1 == length cs2)
             $ throwError $ "Mismatching number of clauses in "
                         ++ show (Case as1 mot1 cs1) ++ " and "
                         ++ show (Case as2 mot2 cs2)
           let argEqs = zipWith Equation as1 as2
           motEqs <- goCaseMotive mot1 mot2
           clauseEqs <- goClauses cs1 cs2
           go (argEqs ++ motEqs ++ clauseEqs ++ eqs) subs'
    go (Equation (OpenIn _ m) (OpenIn _ m'):eqs) subs'
      = go (Equation m m':eqs) subs'
    go (Equation (RecordType tele1) (RecordType tele2):eqs) subs'
      = do eqs' <- goTelescope tele1 tele2
           go (eqs' ++ eqs) subs'
    go (Equation (RecordCon fields1) (RecordCon fields2):eqs) subs'
      = do eqs' <- goFields fields1 fields2
           go (eqs' ++ eqs) subs'
    go (Equation (RecordDot m1 x1) (RecordDot m2 x2):eqs) subs'
      = do unless (x1 == x2)
             $ throwError $ "Field names not equal: " ++ x1 ++ " and " ++ x2
           go (Equation m1 m2:eqs) subs'
    go (Equation m m':_) _ = throwError $ "Terms not equal: " ++ show m ++ " and " ++ show m'
    
    goCaseMotive :: CaseMotive -> CaseMotive -> TypeChecker [Equation]
    goCaseMotive (CaseMotiveNil a1) (CaseMotiveNil a2)
      = return [Equation a1 a2]
    goCaseMotive (CaseMotiveCons a1 sc1) (CaseMotiveCons a2 sc2)
      = do i <- newName
           reqs <- goCaseMotive (instantiate sc1 [Var (Generated i)])
                                (instantiate sc2 [Var (Generated i)])
           return (Equation a1 a2 : reqs)
    goCaseMotive mot mot'
      = throwError $ "Motives not equal: " ++ show mot ++ " and " ++ show mot'
    
    goClauses :: [Clause] -> [Clause] -> TypeChecker [Equation]
    goClauses [] [] = return []
    goClauses (Clause psc1 sc1:cs1) (Clause psc2 sc2:cs2)
      = do is <- replicateM (max (length (names sc1)) (length (names sc2))) newName
           let xs = map Generated is
               xs' = map Var xs
           reqss <- zipWithM goPattern (instantiate psc1 xs) (instantiate psc2 xs)
           reqs' <- goClauses cs1 cs2
           return (Equation (instantiate sc1 xs') (instantiate sc2 xs') : concat reqss ++ reqs')
    goClauses _ _ = throwError $ "Mismatching number of clauses."
    
    goPattern :: Pattern -> Pattern -> TypeChecker [Equation]
    goPattern (VarPat x) (VarPat x')
      = do unless (x == x')
             $ throwError $ "Variable patters not equal: " ++ show x ++ " and " ++ show x'
           return []
    goPattern (ConPat c ps) (ConPat c' ps')
      | c == c'   = goPatterns ps ps'
      | otherwise = throwError $ "Mismatching constructors " ++ show c ++ " and " ++ show c'
    goPattern _ _ = throwError "Patterns not equal."
    
    goPatterns :: [(Plicity,Pattern)] -> [(Plicity,Pattern)] -> TypeChecker [Equation]
    goPatterns [] []
      = return []
    goPatterns ((plic1,p1):ps1) ((plic2,p2):ps2)
      = do unless (plic1 == plic2)
             $ throwError "Mismatched plicities when trying to unify constructor sequences."
           eqs <- goPattern p1 p2
           eqs' <- goPatterns ps1 ps2
           return $ eqs ++ eqs'
    goPatterns _ _
      = throwError "Patterns not equal."
    
    goTelescope :: Telescope -> Telescope -> TypeChecker [Equation]
    goTelescope TelescopeNil TelescopeNil
      = return []
    goTelescope (TelescopeCons x1 t1 sc1) (TelescopeCons x2 t2 sc2)
      = do unless (x1 == x2)
             $ throwError $ "Mismatching record field names: " ++ x1 ++ " and " ++ x2
           eqs' <- goTelescope (descope (Var . Name) sc1) (descope (Var . Name) sc2)
           return (Equation t1 t2:eqs')
    goTelescope _ _
      = throwError "Mismatched number of record fields."
    
    goFields :: [(String,Term)] -> [(String,Term)] -> TypeChecker [Equation]
    goFields [] [] = return []
    goFields (_:_) [] = throwError "Mismatching number of record fields."
    goFields [] (_:_) = throwError "Mismatching number of record fields."
    goFields ((x,m):xms) xms'
      = case extract (\(x',_) -> x == x') xms' of
          Nothing      -> throwError "Mismatching record field names."
          Just ((_,m'),xms'') -> do eqs' <- goFields xms xms''
                                    return (Equation m m':eqs')



addSubstitutions :: Substitution -> TypeChecker ()
addSubstitutions subs0
  = do completeSubstitution subs0
       substituteContext
  where
    
    completeSubstitution subs'
      = do subs <- substitution
           let subs2 = subs' ++ subs
               subs2' = nubBy (\(a,_) (b,_) -> a == b) (map (\(k,v) -> (k, instantiateMetas subs2 v)) subs2)
           putSubstitution subs2'
    
    substituteContext
      = do ctx <- context
           subs <- substitution
           putContext (map (\(x,t) -> (x, instantiateMetas subs t)) ctx)



unify :: Term -> Term -> TypeChecker ()
unify p q = do subs' <- solve [Equation p q]
               addSubstitutions subs'



instantiateMetas :: Substitution -> Term -> Term
instantiateMetas _ (Var x)
  = Var x
instantiateMetas subs (Meta i)
  = case lookup i subs of
      Nothing -> Meta i
      Just t  -> instantiateMetas subs t
instantiateMetas _ (DottedVar m x)
  = DottedVar m x
instantiateMetas subs (Ann m t)
  = Ann (instantiateMetas subs m) (instantiateMetas subs t)
instantiateMetas _ Type
  = Type
instantiateMetas subs (Fun plic a sc)
  = Fun plic
        (instantiateMetas subs a)
        (instantiateMetas subs <$> sc)
instantiateMetas subs (Lam plic sc)
  = Lam plic (instantiateMetas subs <$> sc)
instantiateMetas subs (App plic f a)
  = App plic
        (instantiateMetas subs f)
        (instantiateMetas subs a)
instantiateMetas subs (Con c as)
  = Con c (map (\(plic,a) -> (plic, instantiateMetas subs a)) as)
instantiateMetas subs (Case as mot cs)
  = Case (map (instantiateMetas subs) as)
         (instantiateMetasCaseMotive subs mot)
         (map instantiateClause cs)
  where
    instantiateClause (Clause ps sc)
      = Clause ps (instantiateMetas subs <$> sc)
instantiateMetas subs (OpenIn settings m)
  = OpenIn settings (instantiateMetas subs m)
instantiateMetas subs (RecordType tele)
  = RecordType (instantiateMetasTelescope tele)
  where
    instantiateMetasTelescope TelescopeNil
      = TelescopeNil
    instantiateMetasTelescope (TelescopeCons x t sc)
      = TelescopeCons x
          (instantiateMetas subs t)
          (instantiateMetasTelescope <$> sc)
instantiateMetas subs (RecordCon fields)
  = RecordCon [ (x,instantiateMetas subs m) | (x,m) <- fields ]
instantiateMetas subs (RecordDot m x)
  = RecordDot (instantiateMetas subs m) x

instantiateMetasCaseMotive :: Substitution -> CaseMotive -> CaseMotive
instantiateMetasCaseMotive subs (CaseMotiveNil a)
      = CaseMotiveNil (instantiateMetas subs a)
instantiateMetasCaseMotive subs (CaseMotiveCons a sc)
  = CaseMotiveCons (instantiateMetas subs a)
                   (instantiateMetasCaseMotive subs <$> sc)

instantiateMetasPat :: Substitution -> Pattern -> Pattern
instantiateMetasPat _ (VarPat x)
  = VarPat x
instantiateMetasPat subs (ConPat c ps)
  = ConPat c (map (\(plic,p) -> (plic,instantiateMetasPat subs p)) ps)
instantiateMetasPat subs (AssertionPat m)
  = AssertionPat (instantiateMetas subs m)




unalias :: Either String (String,String) -> TypeChecker (String,String)
unalias (Left n)
  = do als <- aliases
       case lookup (Left n) als of
         Nothing -> throwError $ "The symbol " ++ n ++ " is not an alias for any "
                              ++ "module-declared symbol."
         Just p  -> return p
unalias (Right (m,n))
  = do als <- aliases
       case lookup (Right (m,n)) als of
         Nothing -> throwError $ "The symbol " ++ m ++ "." ++ n ++ " is not an alias for any "
                              ++ "module-declared symbol."
         Just p  -> return p

typeInSignature :: Constructor -> TypeChecker (Constructor, ConSig Term)
typeInSignature (BareCon n0)
  = do (m,n) <- unalias (Left n0)
       typeInSignature (DottedCon m n)
typeInSignature (DottedCon m n)
  = do consigs <- signature
       (m',n') <- catchError
                    (unalias (Right (m,n)))
                    (\_ -> return (m,n))
       case lookup (m',n') consigs of
         Nothing -> throwError $ "Unknown constructor: " ++ show (DottedCon m' n')
         Just t  -> return (DottedCon m' n', t)

dottedTypeInDefinitions :: String -> String -> TypeChecker ((String,String),Term)
dottedTypeInDefinitions m x
  = do (m',x') <- catchError
                    (unalias (Right (m,x)))
                    (\_ -> return (m,x))
       defs <- definitions
       case find (\(mx,_,_) -> mx == (m',x')) defs of
         Nothing      -> throwError $ "Unknown constant/defined term: " ++ m' ++ "." ++ x'
         Just (_,_,t) -> return ((m',x'),t)

typeInDefinitions :: String -> TypeChecker ((String,String),Term)
typeInDefinitions x0
  = do (m,x) <- unalias (Left x0)
       dottedTypeInDefinitions m x

typeInContext :: Int -> TypeChecker Term
typeInContext i
  = do ctx <- context
       case lookup i ctx of
         Nothing -> throwError "Unbound automatically generated variable."
         Just t  -> return t

evaluate :: Term -> TypeChecker Term
evaluate m
  = do defs <- definitions
       case runReaderT (eval m) [ (x,m') | (x,m',_) <- defs ] of
         Left e   -> throwError e
         Right m' -> return m'

ensureOpenSettingsAreValid :: [OpenSettings] -> TypeChecker ()
ensureOpenSettingsAreValid oss
  = forM_ oss $ \(OpenSettings m a hu r) -> do
      ensureModuleExists m
      openAsIsValid a
      hidingUsingIsValid m hu
      renamingIsValid m a hu r
       
  where
    ensureModuleExists :: String -> TypeChecker ()
    ensureModuleExists m
      = do ms <- moduleNames
           unless (m `elem` ms)
             $ throwError $ "The module " ++ m ++ " is not a known module."
    
    openAsIsValid :: Maybe String -> TypeChecker ()
    openAsIsValid Nothing = return ()
    openAsIsValid (Just m')
      = do ms <- moduleNames
           unless (not (m' `elem` ms))
             $ throwError $ "The module name " ++ m' ++ " is already in use."
    
    hidingUsingIsValid :: String -> Maybe HidingUsing -> TypeChecker ()
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
    
    renamingIsValid :: String -> Maybe String -> Maybe HidingUsing -> [(String,String)] -> TypeChecker ()
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
           

extendAliases :: [OpenSettings] -> TypeChecker a -> TypeChecker a
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



-- Type Inference

inferify :: Term -> TypeChecker (Term,Term)
inferify (Meta i)
  = throwError $ "The metavariable " ++ show (Meta i)
              ++ " appears in checkable code, when it should not."
inferify (Var (Name x0))
  = do ((m,x),t) <- typeInDefinitions x0
       return (DottedVar m x, t)
inferify (Var (Generated i))
  = do t <- typeInContext i
       return (Var (Generated i), t)
inferify (DottedVar m x)
  = do ((m',x'),t) <- dottedTypeInDefinitions m x
       return (DottedVar m' x', t)
inferify (Ann m t)
  = do t' <- checkify t Type
       et' <- evaluate t'
       m' <- checkify m et'
       subs <- substitution
       return (instantiateMetas subs m', instantiateMetas subs et')
inferify Type
  = return (Type,Type)
inferify (Fun plic arg sc)
  = do arg' <- checkify arg Type
       i <- newName
       ret' <- extendContext [(i,arg')]
                 $ checkify (instantiate sc [Var (Generated i)]) Type
       let sc' :: Scope Term Term
           sc' = Scope (names sc) (abstractOver [i] ret')
       subs <- substitution
       return (instantiateMetas subs (Fun plic arg' sc'), Type)
inferify (Lam _ _)
  = throwError "Cannot infer the type of a lambda expression."
inferify (App plic f a)
  = do (f0,t0) <- inferify f
       et0 <- evaluate t0
       (app',t') <- insertImplicits f0 plic et0
       subs <- substitution
       return (instantiateMetas subs app', instantiateMetas subs t')
  where
    insertImplicits :: Term -> Plicity -> Term -> TypeChecker (Term,Term)
    insertImplicits f' Expl (Fun Expl arg sc)
      = do earg <- evaluate arg
           a' <- checkify a earg
           return (App Expl f' a', instantiate sc [a'])
    insertImplicits f' Impl (Fun Impl arg sc)
      = do earg <- evaluate arg
           a' <- checkify a earg
           return (App Impl f' a', instantiate sc [a'])
    insertImplicits f' Expl (Fun Impl _ sc)
      = do meta <- newMetaVar
           let impla = Meta meta
               newF' = App Impl f' impla
           newT' <- evaluate (instantiate sc [impla])
           insertImplicits newF' Expl newT'
    insertImplicits _ Impl (Fun Expl _ _)
      = throwError $ "Expected an explicit argument but found an implicit argument "
                  ++ "when applying " ++ show f ++ " to " ++ show a ++ " in "
                  ++ "the expression " ++ show (App plic f a)
    insertImplicits _ _ t
      = throwError $ "Cannot insert implicit arguments for non-function type " ++ show t
inferify (Con c as)
  = do (unaliasedC,consig) <- typeInSignature c
       (as',ret) <- inferifyConArgs consig as consig
       subs <- substitution
       return (instantiateMetas subs (Con unaliasedC as'), instantiateMetas subs ret)
  where
    inferifyConArgs _ [] (ConSigNil ret)
      = return ([], ret)
    inferifyConArgs consig ((Expl,m):ms) (ConSigCons Expl arg sc)
      = do subs <- substitution
           earg <- evaluate (instantiateMetas subs arg)
           m' <- checkify m earg
           (ms',ret) <- inferifyConArgs consig ms (instantiate sc [m])
           return ((Expl,m'):ms', ret)
    inferifyConArgs consig ((Impl,m):ms) (ConSigCons Impl arg sc)
      = do subs <- substitution
           earg <- evaluate (instantiateMetas subs arg)
           m' <- checkify m earg
           (ms',ret) <- inferifyConArgs consig ms (instantiate sc [m])
           return ((Impl,m'):ms', ret)
    inferifyConArgs consig ms (ConSigCons Impl _ sc)
      = do meta <- newMetaVar
           let implm = Meta meta
           (ms',ret) <- inferifyConArgs consig ms (instantiate sc [implm])
           return ((Impl,implm):ms', ret)
    inferifyConArgs consig ((Impl,_):_) (ConSigCons Expl _ _)
      = throwError $ "Expected an explicit argument but found an implicit argument "
                  ++ "when checking " ++ show (Con c as)
                  ++ " matches the signature " ++ showConSig (Var . Name) consig
    inferifyConArgs consig _ _
      = do let las = length as
               lsig = conSigLength (Var . Name) consig
           throwError $ show c ++ " expects " ++ show lsig ++ " "
                   ++ (if lsig == 1 then "arg" else "args")
                   ++ " but was given " ++ show las
inferify (Case ms0 mot cs)
  = do mot' <- checkifyCaseMotive mot
       ms0' <- checkifyCaseArgs ms0 mot'
       cs' <- checkifyClauses cs mot'
       ret <- auxMotive ms0' mot'
       subs <- substitution
       return (instantiateMetas subs (Case ms0' mot' cs'), instantiateMetas subs ret)
  where
    checkifyCaseArgs [] (CaseMotiveNil _)
      = return []
    checkifyCaseArgs (m:ms) (CaseMotiveCons a sc)
      = do ea <- evaluate a
           m' <- checkify m ea
           ms' <- checkifyCaseArgs ms (instantiate sc [m])
           return (m':ms')
    checkifyCaseArgs _ _
      = do let lms = length ms0
               lmot = caseMotiveLength mot
           throwError $ "Motive " ++ show mot ++ " expects " ++ show lmot ++ " case "
                   ++ (if lmot == 1 then "arg" else "args")
                   ++ " but was given " ++ show lms
    
    auxMotive [] (CaseMotiveNil a)
      = return a
    auxMotive (m:ms) (CaseMotiveCons _ sc)
      = auxMotive ms (instantiate sc [m])
    auxMotive _ _
      = do let lms = length ms0
               lmot = caseMotiveLength mot
           throwError $ "Motive " ++ show mot ++ " expects " ++ show lmot ++ " case "
                   ++ (if lmot == 1 then "arg" else "args")
                   ++ " but was given " ++ show lms
inferify (OpenIn settings m)
  = extendAliases settings (inferify m)
inferify (RecordType tele)
  = do tele' <- checkifyTelescope tele
       return (RecordType tele', Type)
  where
    checkifyTelescope TelescopeNil
      = return TelescopeNil
    checkifyTelescope (TelescopeCons x t sc)
      = do t' <- checkify t Type
           i <- newName
           m' <- extendContext [(i,t')]
                   $ checkifyTelescope (instantiate sc [Var (Generated i)])
           return (TelescopeCons x t' (Scope (names sc) (abstractOver [i] m')))
inferify (RecordCon _)
  = throwError "Cannot infer the type of a record expression."
inferify (RecordDot m x)
  = do (m',t) <- inferify m
       case t of
         RecordType tele
            -> case lookupField m' x tele of
                 Nothing -> throwError $ "Missing field " ++ x
                 Just t' -> return (RecordDot m' x, t')
         t' -> throwError $ "Expecting a record type but found " ++ show t'
  where
    lookupField _ _ TelescopeNil = Nothing
    lookupField m' f (TelescopeCons f' t sc)
      | f == f'   = Just t
      | otherwise = lookupField m' f (instantiate sc [RecordDot m' f'])


-- Type Checking
checkify :: Term -> Term -> TypeChecker Term
checkify (Meta i) _
  = throwError $ "The metavariable " ++ show (Meta i)
              ++ " appears in checkable code, when it should not."
checkify (Lam plic sc) t
  = do et <- evaluate t
       case (plic,et) of
         (Expl, Fun Expl arg sc') -> -- \x -> M : (x : A) -> B
           do i <- newName
              eret <- evaluate (instantiate sc' [Var (Generated i)])
              m' <- extendContext [(i,arg)]
                      $ checkify
                          (instantiate sc [Var (Generated i)])
                          eret
              subs <- substitution
              return (instantiateMetas subs (Lam Expl (Scope (names sc) (abstractOver [i] m'))))
         (Impl, Fun Impl arg sc') -> -- \{y} -> M : {y : A} -> B
           do i <- newName
              eret <- evaluate (instantiate sc' [Var (Generated i)])
              m' <- extendContext [(i,arg)]
                      $ checkify
                          (instantiate sc [Var (Generated i)])
                          eret
              subs <- substitution
              return (instantiateMetas subs (Lam Impl (Scope (names sc) (abstractOver [i] m'))))
         (Expl, Fun Impl arg sc') -> -- \x -> M : {y : A} -> B
           do i <- newName
              eret <- evaluate (instantiate sc' [Var (Generated i)])
              f' <- extendContext [(i,arg)]
                      $ checkify
                          (Lam Expl sc)
                          eret
              subs <- substitution
              return (instantiateMetas subs (Lam Impl (Scope ["_"] (abstractOver ([]::[String]) f'))))
         (Impl, Fun Expl _ _) -> -- \{y} -> M : (x : A) -> B
           throwError $ "Expected an explicit argument but found an implicit argument "
                  ++ "when checking " ++ show (Lam plic sc)
                  ++ " matches the signature " ++ show t
         _ -> throwError $ "Cannot check term: " ++ show (Lam plic sc) ++ "\n"
              ++ "Against non-function type: " ++ show t
checkify (Con c as) t
  = do (unaliasedC,consig) <- typeInSignature c
       (ats, ret) <- dropConArgs as consig
       unify t ret
       as' <- mapM checkifyConArg ats
       subs <- substitution
       return (instantiateMetas subs (Con unaliasedC as'))
  where
    dropConArgs :: [(Plicity,Term)] -> ConSig Term -> TypeChecker ([Either (Plicity,Term) (Plicity,Term,Term)], Term)
    dropConArgs [] (ConSigNil ret)
      = return ([], ret)
    dropConArgs ((Expl,m):ms) (ConSigCons Expl arg sc)
      = do (ats,ret) <- dropConArgs ms (instantiate sc [m])
           return (Right (Expl,m,arg):ats, ret)
    dropConArgs ((Impl,m):ms) (ConSigCons Impl arg sc)
      = do (ats,ret) <- dropConArgs ms (instantiate sc [m])
           return (Right (Impl,m,arg):ats, ret)
    dropConArgs ms (ConSigCons Impl _ sc)
      = do meta <- newMetaVar
           let x = Meta meta
           (ats,ret) <- dropConArgs ms (instantiate sc [x])
           return (Left (Impl,x):ats,ret)
    dropConArgs ((Impl,_):_) (ConSigCons Expl _ _)
      = throwError $ "Mismatching plicits when checking " ++ show (Con c as)
                  ++ " has type " ++ show t
    dropConArgs _ _
      = throwError $ "Mismatching number of arguments when checking " ++ show (Con c as)
                  ++ " has type " ++ show t
    
    checkifyConArg :: Either (Plicity,Term) (Plicity,Term,Term) -> TypeChecker (Plicity,Term)
    checkifyConArg (Left pm)
      = return pm
    checkifyConArg (Right (plic, m, arg))
      = do subs <- substitution
           earg <- evaluate (instantiateMetas subs arg)
           m' <- checkify m earg
           return (plic,m')
checkify (RecordCon fields) t
  = case t of
      RecordType tele
        -> do fields' <- checkifyFields fields tele
              return $ RecordCon fields'
      _ -> throwError $ "Cannot check a record against type " ++ show t
  where
    checkifyFields [] TelescopeNil
      = return []
    checkifyFields [] (TelescopeCons x _ _)
      = throwError $ "Missing record field " ++ x
    checkifyFields _ TelescopeNil
      = throwError $ "Mismatching number of record fields."
    checkifyFields xs (TelescopeCons x t' sc)
      = case extract (\(x',_) -> x == x') xs of
          Nothing -> throwError $ "Missing record field " ++ x
          Just ((_,m),xs') -> do
            et' <- evaluate t'
            m' <- checkify m et'
            fields' <- checkifyFields xs' (instantiate sc [m'])
            return ((x,m'):fields')
checkify m t
  = do (m',t') <- inferify m
       et <- evaluate t
       et' <- evaluate t'
       unify et et'
       subs <- substitution
       return (instantiateMetas subs m')


checkifyCaseMotive :: CaseMotive -> TypeChecker CaseMotive
checkifyCaseMotive (CaseMotiveNil a)
  = do a' <- checkify a Type
       return (CaseMotiveNil a')
checkifyCaseMotive (CaseMotiveCons a sc)
  = do a' <- checkify a Type
       i <- newName
       b' <- extendContext [(i,a')]
               $ checkifyCaseMotive (instantiate sc [Var (Generated i)])
       subs <- substitution
       return (instantiateMetasCaseMotive subs (CaseMotiveCons a' (Scope (names sc) (abstractOver [i] b'))))


checkifyPattern :: Pattern -> Term -> TypeChecker (Pattern,Term)
checkifyPattern (VarPat (Name x)) _
  = return (VarPat (Name x), Var (Name x))
checkifyPattern (VarPat (Generated i)) t
  = do t' <- typeInContext i
       unify t t'
       return (VarPat (Generated i), Var (Generated i))
checkifyPattern (ConPat c ps0) t
  = do (unaliasedC,sig) <- typeInSignature c
       (ps',xs,ret) <- checkifyPatConArgs sig ps0 sig
       subs <- substitution
       et <- evaluate (instantiateMetas subs t)
       eret <- evaluate (instantiateMetas subs ret)
       unify et eret
       subs' <- substitution
       return ( instantiateMetasPat subs' (ConPat unaliasedC ps')
              , instantiateMetas subs' (Con unaliasedC xs)
              )
  where
    checkifyPatConArgs :: ConSig Term -> [(Plicity,Pattern)] -> ConSig Term -> TypeChecker ([(Plicity,Pattern)],[(Plicity,Term)],Term)
    checkifyPatConArgs _ [] (ConSigNil ret)
      = return ([],[],ret)
    checkifyPatConArgs consig ((Expl,p):ps) (ConSigCons Expl arg sc')
      = do earg <- evaluate arg
           (p',x) <- checkifyPattern p earg
           (ps',xs,ret) <-
             checkifyPatConArgs consig ps (instantiate sc' [x])
           return ( (Expl,p'):ps'
                  , (Expl,x):xs
                  , ret
                  )
    checkifyPatConArgs consig ((Impl,p):ps) (ConSigCons Impl arg sc')
      = do earg <- evaluate arg
           (p',x) <- checkifyPattern p earg
           (ps',xs,ret) <-
             checkifyPatConArgs consig ps (instantiate sc' [x])
           return ( (Impl,p'):ps'
                  , (Impl,x):xs
                  , ret
                  )
    checkifyPatConArgs consig ps (ConSigCons Impl _ sc')
      = do meta <- newMetaVar
           let x = Meta meta
           (ps',xs,ret) <- checkifyPatConArgs
                             consig
                             ps
                             (instantiate sc' [x])
           return ( (Impl,AssertionPat x):ps'
                  , (Impl,x):xs
                  , ret
                  )
    checkifyPatConArgs consig ((Impl,_):_) (ConSigCons Expl _ _)
      = throwError $ "Expected an explicit argument but found an implicit argument "
                  ++ "when checking " ++ show (ConPat c ps0)
                  ++ " matches the signature " ++ showConSig (Var . Name) consig
    checkifyPatConArgs consig _ _
      = do let lps = length ps0
               lsig = conSigLength (Var . Name) consig
           throwError $ show c ++ " expects " ++ show lsig ++ " case "
                   ++ (if lsig == 1 then "arg" else "args")
                   ++ " but was given " ++ show lps
checkifyPattern (AssertionPat m) t
  = do m' <- checkify m t
       subs <- substitution
       let m'' = instantiateMetas subs m'
       return (AssertionPat m'', m'')


checkifyClause :: Clause -> CaseMotive -> TypeChecker Clause
checkifyClause (Clause psc sc0) motive
  = do ctx <- replicateM (length (names sc0)) $ do
                i <- newName
                m <- newMetaVar
                return (i, Meta m)
       let is = map fst ctx
       extendContext ctx $ do
         (ps',ret) <- checkPatternsMotive (instantiate psc (map Generated is)) motive
         eret <- evaluate ret
         m' <- checkify (instantiate sc0 (map (Var . Generated) is)) eret
         return $ Clause (Scope (names psc) (abstractOver is ps'))
                         (Scope (names sc0) (abstractOver is m'))
  where
    checkPatternsMotive :: [Pattern] -> CaseMotive -> TypeChecker ([Pattern],Term)
    checkPatternsMotive [] (CaseMotiveNil ret)
      = return ([],ret)
    checkPatternsMotive (p:ps) (CaseMotiveCons arg sc')
      = do earg <- evaluate arg
           (p',x) <- checkifyPattern p earg
           (ps',ret) <-
             checkPatternsMotive ps (instantiate sc' [x])
           return ( p':ps'
                  , ret
                  )
    checkPatternsMotive _ _
      = do let lps = length (descope Name psc)
               lmot = caseMotiveLength motive
           throwError $ "Motive " ++ show motive ++ " expects " ++ show lmot ++ " case "
                   ++ (if lmot == 1 then "arg" else "args")
                   ++ " but was given " ++ show lps


checkifyClauses :: [Clause] -> CaseMotive -> TypeChecker [Clause]
checkifyClauses [] _
  = return []
checkifyClauses (c:cs) motive
  = do c' <- checkifyClause c motive
       cs' <- checkifyClauses cs motive
       return (c':cs')

checkifyConSig :: ConSig Term -> TypeChecker (ConSig Term)
checkifyConSig (ConSigNil ret)
  = do ret' <- checkify ret Type
       return (ConSigNil ret')
checkifyConSig (ConSigCons plic arg sc)
  = do arg' <- checkify arg Type
       i <- newName
       t <- extendContext [(i,arg')]
              $ checkifyConSig (instantiate sc [Var (Generated i)])
       return (ConSigCons plic arg' (Scope (names sc) (abstractOver [i] t)))




-- type checking succees exactly when checkification succeeds
-- and there is a substitution for every meta-variable


metasSolved :: TypeChecker ()
metasSolved = do s <- get
                 unless (tcNextMeta s == length (tcSubs s))
                   $ throwError "Not all metavariables have been solved."

check :: Term -> Term -> TypeChecker Term
check m t = do et <- evaluate t
               m' <- checkify m et
               metasSolved
               subs <- substitution
               return (instantiateMetas subs m')
                
infer :: Term -> TypeChecker (Term,Term)
infer m = do (m',t) <- inferify m
             metasSolved
             subs <- substitution
             et <- evaluate (instantiateMetas subs t)
             return (instantiateMetas subs m', et)