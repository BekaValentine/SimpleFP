{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Dependent.Core.Parser where

import Control.Applicative ((<$>),(<*>),(*>),(<*))
import Control.Monad.Reader
import Data.List (foldl')
import Text.Parsec
import qualified Text.Parsec.Token as Token

import Abs
import Scope
import Dependent.Core.Term
import Dependent.Core.Program




-- Abstraction

abstractClause :: Clause -> Abstracted String Term Clause
abstractClause (Clause p sc)
  = Clause p <$> abstractScope sc

abstractSeqClause :: SeqClause -> Abstracted String Term SeqClause
abstractSeqClause (SeqClause ps sc)
  = SeqClause ps <$> abstractScope sc

instance Abstract String Term CasesArgType where
  abstract (CasesArgNil a)
    = CasesArgNil <$> abstract a
  abstract (CasesArgCons a sc)
    = CasesArgCons <$> abstract a <*> abstractScope sc

instance Abstract String Term Term where
  abstract (Var (Name x))
    = reader $ \e ->
        case lookup x e of
          Nothing -> Var (Name x)
          Just m  -> m
  abstract (Var (Generated i))
    = return $ Var (Generated i)
  abstract (Ann m ty)
    = Ann <$> abstract m <*> return ty
  abstract Type
    = return Type
  abstract (Fun a sc)
    = Fun <$> abstract a <*> abstractScope sc
  abstract (Lam sc)
    = Lam <$> abstractScope sc
  abstract (App f a)
    = App <$> abstract f <*> abstract a
  abstract (Con c as)
    = Con c <$> mapM abstract as
  abstract (Case a cs)
    = Case <$> abstract a <*> mapM abstractClause cs
  abstract (Cases as t cs)
    = Cases <$> mapM abstract as <*> abstract t <*> mapM abstractSeqClause cs

funHelper :: String -> Term -> Term -> Term
funHelper x a b = Fun a (Scope $ \[x'] -> runReader (abstract b) [(x,x')])

lamHelper :: String -> Term -> Term
lamHelper x b = Lam (Scope $ \[a] -> runReader (abstract b) [(x,a)])

clauseHelper :: Pattern -> [String] -> Term -> Clause
clauseHelper p xs b = Clause p (Scope $ \as -> runReader (abstract b) (zip xs as))

seqClauseHelper :: [Pattern] -> [String] -> Term -> SeqClause
seqClauseHelper ps xs b = SeqClause ps (Scope $ \as -> runReader (abstract b) (zip xs as))

consCasesArgTypeHelper :: String -> Term -> CasesArgType -> CasesArgType
consCasesArgTypeHelper x a b = CasesArgCons a (Scope $ \[x'] -> runReader (abstract b) [(x,x')])




-- Language Definition

languageDef :: Token.LanguageDef st
languageDef = Token.LanguageDef
              { Token.commentStart = "{-"
              , Token.commentEnd = "-}"
              , Token.commentLine = "--"
              , Token.nestedComments = True
              , Token.identStart = letter <|> char '_'
              , Token.identLetter = alphaNum <|> char '_' <|> char '\''
              , Token.opStart = oneOf ""
              , Token.opLetter = oneOf ""
              , Token.reservedNames = ["data","case","cases","of","end","where","let","Type"]
              , Token.reservedOpNames = ["|","||","->","\\",":","::","="]
              , Token.caseSensitive = True
              }

tokenParser = Token.makeTokenParser languageDef

identifier = Token.identifier tokenParser
reserved = Token.reserved tokenParser
reservedOp = Token.reservedOp tokenParser
parens = Token.parens tokenParser





-- names

varName = do lookAhead lower
             identifier

decName = do lookAhead upper
             identifier


-- term parsers

variable = Var <$> (Name <$> varName)

annotation = do m <- try $ do
                  m <- annLeft
                  _ <- reservedOp ":"
                  return m
                t <- annRight
                return $ Ann m t

typeType = do _ <- reserved "Type"
              return Type

funType = do (x,arg) <- parens $ do
                        x <- varName
                        _ <- reservedOp ":"
                        arg <- funArg
                        return (x,arg)
             _ <- reservedOp "->"
             ret <- funRet
             return $ funHelper x arg ret --Fun x arg ret

lambda = do _ <- reservedOp "\\"
            x <- varName
            _ <- reservedOp "->"
            b <- lamBody
            return $ lamHelper x b --Lam x b

application = do (f,a) <- try $ do
                   f <- appFun
                   a <- appArg
                   return (f,a)
                 as <- many appArg
                 return $ foldl' App f (a:as)

noArgConData = do c <- decName
                  return $ Con c []

conData = do c <- decName
             as <- many conArg
             return $ Con c as

varPattern = do x <- varName
                return (VarPat,[x])

noArgConPattern = do c <- decName
                     return $ (ConPat c [], [])

conPattern = do c <- decName
                psxs <- many conPatternArg
                let (ps,xs) = unzip psxs
                return $ (ConPat c ps, concat xs)

parenPattern = parens pattern

conPatternArg = parenPattern <|> noArgConPattern <|> varPattern

pattern = parenPattern <|> conPattern <|> varPattern

clause = do (p,xs) <- try $ do
              pxs <- pattern
              _ <- reservedOp "->"
              return pxs
            b <- term
            return $ clauseHelper p xs b

caseExp = do _ <- reserved "case"
             m <- caseArg
             _ <- reserved "of"
             _ <- optional (reservedOp "|")
             cs <- clause `sepBy` reservedOp "|"
             _ <- reserved "end"
             return $ Case m cs

consCasesArgType = do (x,a) <- try $ parens $ do
                        x <- varName
                        _ <- reservedOp ":"
                        a <- term
                        return (x,a)
                      _ <- reservedOp "||"
                      b <- casesArgType
                      return $ consCasesArgTypeHelper x a b

nilCasesArgType = CasesArgNil <$> term

parenCasesArgType = parens casesArgType

casesArgType = parenCasesArgType <|> consCasesArgType <|> nilCasesArgType

seqClause = do psxs <- try $ do
                 psxs <- pattern `sepBy1` reservedOp "||"
                 _ <- reservedOp "->"
                 return psxs
               let (ps,xss) = unzip psxs
                   xs = concat xss
               b <- term
               return $ seqClauseHelper ps xs b

casesExp = do _ <- reserved "cases"
              ms <- caseArg `sepBy1` reservedOp "||"
              _ <- reservedOp "::"
              t <- casesArgType
              _ <- reserved "of"
              _ <- optional (reservedOp "|")
              cs <- seqClause `sepBy` reservedOp "|"
              _ <- reserved "end"
              return $ Cases ms t cs

parenTerm = parens term

annLeft = application <|> parenTerm <|> conData <|> variable <|> typeType

annRight = funType <|> application <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType

funArg = annotation <|> funType <|> application <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType

funRet = annotation <|> funType <|> application <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType

lamBody = annotation <|> funType <|> application <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType

appFun = parenTerm <|> variable <|> typeType

appArg = parenTerm <|> noArgConData <|> variable <|> typeType

conArg = parenTerm <|> noArgConData <|> variable <|> typeType

caseArg = annotation <|> funType <|> application <|> parenTerm <|> lambda <|> conData <|> variable <|> typeType

term = annotation <|> funType <|> application <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType

parseTerm str = case parse (spaces *> term <* eof) "(unknown)" str of
                  Left e -> Left (show e)
                  Right p -> Right p



-- program parsers

termDecl = do _ <- reserved "let"
              x <- varName
              _ <- reservedOp ":"
              t <- term
              _ <- reservedOp "="
              m <- term
              _ <- reserved "end"
              return $ TermDeclaration x t m

alternative = do c <- decName
                 as <- many alternativeArg
                 _ <- reservedOp ":"
                 t <- term
                 return (c,as,t)

alternativeArg = parens $ do
                   x <- varName
                   _ <- reservedOp ":"
                   t <- term
                   return $ DeclArg x t

emptyTypeDecl = do _ <- reserved "data"
                   tycon <- decName
                   tyargs <- many typeArg
                   _ <- reserved "end"
                   return $ TypeDeclaration tycon tyargs []

nonEmptyTypeDecl = do _ <- reserved "data"
                      tycon <- decName
                      tyargs <- many typeArg
                      _ <- reserved "where"
                      _ <- optional (reservedOp "|")
                      alts <- alternative `sepBy` reservedOp "|"
                      _ <- reserved "end"
                      return $ TypeDeclaration tycon tyargs alts

typeArg = parens $ do
            x <- varName
            _ <- reservedOp ":"
            t <- term
            return $ DeclArg x t

typeDecl = emptyTypeDecl <|> nonEmptyTypeDecl

statement = TmDecl <$> termDecl
        <|> TyDecl <$> typeDecl

program = Program <$> many statement



parseProgram :: String -> Either String Program
parseProgram str
  = case parse (spaces *> program <* eof) "(unknown)" str of
      Left e -> Left (show e)
      Right p -> Right p