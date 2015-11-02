{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Record.Core.Term where

import Data.List (intercalate)

import Parens
import Plicity
import Scope





-- Used in multiple places

data DeclArg
  = DeclArg Plicity String Term

instance Show DeclArg where
  show (DeclArg Expl x t) = "(" ++ x ++ " : " ++ show t ++ ")"
  show (DeclArg Impl x t) = "{" ++ x ++ " : " ++ show t ++ "}"

data HidingUsing
  = Hiding [String]
  | Using [String]

data OpenSettings
  = OpenSettings
    { openModule :: String
    , openAs :: Maybe String
    , openHidingUsing :: Maybe HidingUsing
    , openRenaming :: [(String,String)]
    }

instance Show OpenSettings where
  show (OpenSettings m a hu r)
    = m ++ a' ++ hu' ++ r'
    where
      a' = case a of
             Nothing -> ""
             Just m' -> " as " ++ m'
      hu' = case hu of
              Nothing -> ""
              Just (Hiding ns) -> " hiding (" ++ intercalate "," ns ++ ")"
              Just (Using ns)  -> " using (" ++ intercalate "," ns ++ ")"
      r' = case r of
             [] -> ""
             _ -> " renaming (" ++ intercalate ", " [ n ++ " to " ++ n' | (n,n') <- r ] ++ ")"




-- Terms

data Variable
  = Name String
  | Generated Int
  deriving (Eq)

data Constructor
  = BareCon String
  | DottedCon String String
  deriving (Eq)

instance Show Constructor where
  show (BareCon con) = con
  show (DottedCon m con) = m ++ "." ++ con

data Telescope
  = TelescopeNil
  | TelescopeCons String Term (Scope Term Telescope)

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
  | OpenIn [OpenSettings] Term
  | RecordType Telescope
  | RecordCon [(String,Term)]
  | RecordDot Term String

data CaseMotive
  = CaseMotiveNil Term
  | CaseMotiveCons Term (Scope Term CaseMotive)

data Clause
  = Clause PatternSeq (Scope Term Term)

data Pattern
  = VarPat String
  | ConPat Constructor PatternSeq
  | AssertionPat Term

data PatternSeq
  = PatternSeqNil
  | PatternSeqCons Plicity Pattern (Scope Term PatternSeq)




-- Case Motive Length

caseMotiveLength :: CaseMotive -> Int
caseMotiveLength (CaseMotiveNil _) = 0
caseMotiveLength (CaseMotiveCons _ sc)
  = 1 + caseMotiveLength (descope (Var . Name) sc)

-- Pattern Sequence Length
patternSeqLength :: PatternSeq -> Int
patternSeqLength PatternSeqNil = 0
patternSeqLength (PatternSeqCons _ _ sc)
  = 1 + patternSeqLength (descope (Var . Name) sc)




-- Show Instances

instance Show Variable where
  show (Name x) = x
  show (Generated i) = "_" ++ show i

data PatternParenLoc = ExplConPatArg | ImplConPatArg
  deriving (Eq)

instance ParenLoc Pattern where
  type Loc Pattern = PatternParenLoc
  parenLoc (VarPat _)       = [ExplConPatArg,ImplConPatArg]
  parenLoc (ConPat _ _)     = [ImplConPatArg]
  parenLoc (AssertionPat _) = [ExplConPatArg,ImplConPatArg]

instance ParenRec Pattern where
  parenRec (VarPat x)
    = x
  parenRec (ConPat c ps)
    = case auxPatternSeq ps of
        Nothing  -> show c
        Just ps' -> show c ++ " " ++ unwords ps'
    where
      auxPatternSeq :: PatternSeq -> Maybe [String]
      auxPatternSeq PatternSeqNil
        = Nothing
      auxPatternSeq (PatternSeqCons plic p sc)
        = let p0' = parenthesize Nothing p
              p' = case plic of
                     Expl -> p0'
                     Impl -> "{" ++ p0' ++ "}"
              mps' = auxPatternSeq (descope (Var . Name) sc)
          in case mps' of
               Nothing  -> Just [p']
               Just ps' -> Just (p':ps')
  parenRec (AssertionPat m)
    = "." ++ parenthesize (Just AssertionPatArg) m

instance Show Pattern where
  show p = parenthesize Nothing p

instance Show PatternSeq where
  show PatternSeqNil = ""
  show (PatternSeqCons plic arg sc)
    = let arg0' = show arg
          arg' = case plic of
                   Expl -> arg0'
                   Impl -> "{" ++ arg0' ++ "}"
      in case descope (Var . Name) sc of
           PatternSeqNil -> arg'
           ret           -> arg' ++ " || " ++ show ret

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
  parenLoc (OpenIn _ _)
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
    = "cases " ++ intercalate " || " (map (parenthesize Nothing) ms)
   ++ " motive " ++ show mot
   ++ " of " ++ intercalate " | " (map auxClause cs) ++ " end"
    where
      auxClause (Clause ps sc)
        = intercalate " || " (auxPatternSeq ps)
          ++ " -> " ++ parenthesize Nothing
                         (descope (Var . Name) sc)
      
      auxPatternSeq :: PatternSeq -> [String]
      auxPatternSeq PatternSeqNil
        = []
      auxPatternSeq (PatternSeqCons _ p sc)
        = let p' = parenthesize Nothing p
              ps' = auxPatternSeq (descope (Var . Name) sc)
          in p':ps'
  parenRec (OpenIn settings m)
    = "open " ++ intercalate " | " (map show settings) ++ " in " ++ parenthesize Nothing m ++ " end"
  parenRec (RecordType tele)
    = case auxTelescope tele of
        [] -> "Rec {}"
        fields -> "Rec { " ++ intercalate ", " fields ++ " }"
    where
      auxTelescope :: Telescope -> [String]
      auxTelescope TelescopeNil = []
      auxTelescope (TelescopeCons x t sc)
        = let f = x ++ " : " ++ parenthesize Nothing t
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