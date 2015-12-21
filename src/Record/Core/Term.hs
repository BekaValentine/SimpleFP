{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Record.Core.Term where

import Data.List (intercalate,nub)

import Parens
import Plicity
import Scope





-- Used in multiple places

data DeclArg
  = DeclArg Plicity String Term

instance Show DeclArg where
  show (DeclArg Expl x t) = "(" ++ x ++ " : " ++ show t ++ ")"
  show (DeclArg Impl x t) = "{" ++ x ++ " : " ++ show t ++ "}"




-- Terms

data Variable
  = Name String
  | Generated String Int

instance Eq Variable where
  Name x == Name y = x == y
  Generated _ i == Generated _ j = i == j
  _ == _ = False

data Constructor
  = BareCon String
  | DottedCon String String
  deriving (Eq)

instance Show Constructor where
  show (BareCon con) = con
  show (DottedCon m con) = m ++ "." ++ con

data Telescope
  = TelescopeNil
  | TelescopeCons Term (Scope Term Telescope)

data Term
  = Meta Int
  | Var Variable
  | DottedVar String String
  | Ann Term Term
  | Type
  | Fun Plicity Term (Scope Term Term)
  | Lam Plicity (Scope Term Term)
  | App Plicity Term Term
  | Con Constructor [(Plicity, Term)]
  | Case [Term] CaseMotive [Clause]
  | RecordType Telescope
  | RecordCon [(String,Term)]
  | RecordDot Term String

data CaseMotive
  = CaseMotiveNil Term
  | CaseMotiveCons Term (Scope Term CaseMotive)

data Clause
  = Clause (Scope Variable [Pattern]) (Scope Term Term)

data Pattern
  = VarPat Variable
  | ConPat Constructor [(Plicity,Pattern)]
  | AssertionPat Term
  | MakeMeta




-- Case Motive Length

caseMotiveLength :: CaseMotive -> Int
caseMotiveLength (CaseMotiveNil _) = 0
caseMotiveLength (CaseMotiveCons _ sc)
  = 1 + caseMotiveLength (descope (Var . Name) sc)




-- Show Instances

instance Show Variable where
  show (Name x) = x
  show (Generated x _) = x

data PatternParenLoc = ExplConPatArg | ImplConPatArg
  deriving (Eq)

instance ParenLoc Pattern where
  type Loc Pattern = PatternParenLoc
  parenLoc (VarPat _)       = [ExplConPatArg,ImplConPatArg]
  parenLoc (ConPat _ _)     = [ImplConPatArg]
  parenLoc (AssertionPat _) = [ExplConPatArg,ImplConPatArg]
  parenLoc MakeMeta         = [ExplConPatArg,ImplConPatArg]

instance ParenRec Pattern where
  parenRec (VarPat x)
    = show x
  parenRec (ConPat c [])
    = show c
  parenRec (ConPat c ps)
    = show c ++ " " ++ unwords (map auxConPatArg ps)
    where
      auxConPatArg :: (Plicity,Pattern) -> String
      auxConPatArg (Expl,p) = parenthesize (Just ExplConPatArg) p
      auxConPatArg (Impl,p) = "{" ++ parenthesize (Just ImplConPatArg) p ++ "}"
  parenRec (AssertionPat m)
    = "." ++ parenthesize (Just AssertionPatArg) m
  parenRec MakeMeta
    = "?makemeta"

instance Show Pattern where
  show p = parenthesize Nothing p

data TermParenLoc
  = RootTerm
  | AnnLeft | AnnRight
  | FunArg | FunRet
  | LamBody | AppLeft | ExplAppRight | ImplAppRight
  | ExplConArg | ImplConArg | AssertionPatArg
  | RecDotArg
  deriving (Eq)

instance ParenLoc Term where
  type Loc Term = TermParenLoc
  parenLoc (Meta _)
    = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg,RecDotArg]
  parenLoc (Var _)
    = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg,RecDotArg]
  parenLoc (DottedVar _ _)
    = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg,RecDotArg]
  parenLoc (Ann _ _)
    = [FunArg,FunRet,LamBody,ImplAppRight,ImplConArg]
  parenLoc Type
    = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg,RecDotArg]
  parenLoc (Fun _ _ _)
    = [FunArg,FunRet,LamBody,ImplAppRight,ImplConArg]
  parenLoc (Lam _ _)
    = [FunArg,FunRet,LamBody,ImplAppRight,ImplConArg]
  parenLoc (App _ _ _)
    = [FunArg,FunRet,AnnLeft,LamBody,AppLeft,ImplAppRight,ImplConArg]
  parenLoc (Con _ [])
    = [FunArg,FunRet,AnnLeft,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg]
  parenLoc (Con _ _)
    = [FunArg,FunRet,AnnLeft,LamBody,ImplAppRight,ImplConArg]
  parenLoc (Case _ _ _)
    = [FunArg,FunRet,LamBody,ImplAppRight,ImplConArg]
  parenLoc (RecordType _)
    = [FunArg,FunRet,AnnLeft,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg,RecDotArg]
  parenLoc (RecordCon _)
    = [FunArg,FunRet,AnnLeft,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg,RecDotArg]
  parenLoc (RecordDot _ _)
    = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg,RecDotArg]

instance ParenRec Term where
  parenRec (Meta i)
    = "?" ++ show i
  parenRec (Var x)
    = show x
  parenRec (DottedVar m x)
    = m ++ "." ++ x
  parenRec (Ann m ty)
    = parenthesize (Just AnnLeft) m ++ " : " ++ parenthesize (Just AnnRight) ty
  parenRec Type
    = "Type"
  parenRec (Fun plic a sc)
    = let a0' = unwords (names sc) ++ " : " ++ parenthesize (Just FunArg) a
          a' = case plic of
                 Expl -> "(" ++ a0' ++ ")"
                 Impl -> "{" ++ a0' ++ "}"
      in a' ++ " -> "
      ++ parenthesize (Just FunRet)
           (descope (Var . Name) sc)
  parenRec (Lam plic sc)
    = let n0' = unwords (names sc)
          n' = case plic of
                 Expl -> n0'
                 Impl -> "{" ++ n0' ++ "}"
      in "\\" ++ n'
      ++ " -> " ++ parenthesize (Just LamBody)
                     (descope (Var . Name) sc)
  parenRec (App plic f a)
    = let a' = case plic of
                 Expl -> parenthesize (Just ExplAppRight) a
                 Impl -> "{" ++ parenthesize (Just ImplAppRight) a ++ "}"
      in parenthesize (Just AppLeft) f ++ " " ++ a'
  parenRec (Con c [])
    = show c
  parenRec (Con c as)
    = let as' = [ case plic of
                    Expl -> parenthesize (Just ExplConArg) a
                    Impl -> "{" ++ parenthesize (Just ImplConArg) a ++ "}"
                | (plic,a) <- as
                ]
      in show c ++ " " ++ intercalate " " as'
  parenRec (Case ms mot cs)
    = "case " ++ intercalate " || " (map (parenthesize Nothing) ms)
   ++ " motive " ++ show mot
   ++ " of " ++ intercalate " | " (map auxClause cs) ++ " end"
    where
      auxClause (Clause psc sc)
        = intercalate " || " (map show (descope Name psc))
          ++ " -> " ++ parenthesize Nothing
                         (descope (Var . Name) sc)
  parenRec (RecordType tele)
    = case auxTelescope tele of
        [] -> "Rec {}"
        fields -> "Rec { " ++ intercalate ", " fields ++ " }"
    where
      auxTelescope :: Telescope -> [String]
      auxTelescope TelescopeNil = []
      auxTelescope (TelescopeCons t sc)
        = let f = unwords (names sc) ++ " : " ++ parenthesize Nothing t
              fs = auxTelescope (descope (Var . Name) sc)
          in f:fs
  parenRec (RecordCon fields)
    = if null fields
      then "{}"
      else "{ " ++ intercalate ", " [ x ++ " = " ++ parenthesize Nothing t | (x,t) <- fields ] ++ " }"
  parenRec (RecordDot m x)
    = parenthesize (Just RecDotArg) m ++ "." ++ x
      


instance Show Term where
  show t = parenthesize Nothing t



instance Show CaseMotive where
  show (CaseMotiveNil ret) = show ret
  show (CaseMotiveCons arg sc)
    = "(" ++ unwords (names sc) ++ " : " ++ show arg ++ ") || "
   ++ show (descope (Var . Name) sc)



patternVars :: Pattern -> [Variable]
patternVars (VarPat v) = [v]
patternVars (ConPat _ ps) = ps >>= (patternVars . snd)
patternVars (AssertionPat _) = []
patternVars MakeMeta = []

metas :: Term -> [Int]
metas x = nub (go x)
  where
    go (Meta i) = [i]
    go (Var _) = []
    go (DottedVar _ _) = []
    go (Ann m t) = go m ++ go t
    go Type = []
    go (Fun _ a sc) = go a ++ go (descope (Var . Name) sc)
    go (Lam _ sc) = go (descope (Var . Name) sc)
    go (App _ f x) = go f ++ metas x
    go (Con _ xs) = concat (map (go . snd) xs)
    go (Case as mot cs) = concat (map go as) ++ goCaseMotive mot ++ concat (map goClause cs)
    go (RecordType tele) = goTele tele
    go (RecordCon fields) = concat (map (go . snd) fields)
    go (RecordDot m _) = go m

    goPat (VarPat _) = []
    goPat (ConPat _ ps) = concat (map (goPat . snd) ps)
    goPat (AssertionPat m) = go m
    goPat MakeMeta = []
    
    goCaseMotive (CaseMotiveNil t) = go t
    goCaseMotive (CaseMotiveCons a sc) = go a ++ goCaseMotive (descope (Var . Name) sc)
    
    goClause (Clause psc sc) = concat (map goPat (descope Name psc)) ++ go (descope (Var . Name) sc)
    
    goTele TelescopeNil = []
    goTele (TelescopeCons m sc) = go m ++ goTele (descope (Var . Name) sc)

termToPattern :: Term -> Pattern
termToPattern (Var x) = VarPat x
termToPattern (Con c xs) = ConPat c [ (plic, termToPattern x) | (plic,x) <- xs ]
termToPattern m = AssertionPat m