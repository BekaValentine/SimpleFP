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
import Dependent.Core.Abstraction
import Dependent.Core.ConSig
import Dependent.Core.Term
import Dependent.Core.Program




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
              , Token.reservedNames = ["data","case","motive","of","end","where","let","Type"]
              , Token.reservedOpNames = ["|","||","->","\\",":","::","=","."]
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

assertionPattern = do _ <- reservedOp "."
                      m <- assertionPatternArg
                      return $ (AssertionPat m, [])

varPattern = do x <- varName
                return (VarPat x,[x])

noArgConPattern = do c <- decName
                     return $ (ConPat c PatternSeqNil, [])

conPattern = do c <- decName
                psxs <- many conPatternArg
                let (ps,xs) = patternSeqAndNames psxs
                return $ (ConPat c ps, xs)
  where
    patternSeqAndNames :: [(Pattern,[String])] -> (PatternSeq,[String])
    patternSeqAndNames []
      = (PatternSeqNil, [])
    patternSeqAndNames ((p,xs):psxs)
      = let (ps,xs') = patternSeqAndNames psxs
        in (patternSeqHelper p xs ps, xs++xs')

parenPattern = parens pattern

conPatternArg = assertionPattern <|> parenPattern <|> noArgConPattern <|> varPattern

assertionPatternArg = parenTerm <|> noArgConData <|> variable <|> typeType

pattern = assertionPattern <|> parenPattern <|> conPattern <|> varPattern

patternSeqConsNil = do (p,xs) <- pattern
                       return (PatternSeqCons p (Scope xs $ \_ -> PatternSeqNil), xs)

patternSeqCons = do (p,xs) <- try $ do
                      pxs <- pattern
                      _ <- reservedOp "||"
                      return pxs
                    (ps,xs') <- patternSeq
                    return (patternSeqHelper p xs ps,xs++xs')

patternSeq = patternSeqCons <|> patternSeqConsNil

consMotive = do (x,a) <- try $ parens $ do
                  x <- varName
                  _ <- reservedOp ":"
                  a <- term
                  return (x,a)
                _ <- reservedOp "||"
                b <- caseMotive
                return $ consMotiveHelper x a b

nilMotive = CaseMotiveNil <$> term

caseMotive = consMotive <|> nilMotive

clause = do (ps,xs) <- try $ do
              psxs <- patternSeq
              _ <- reservedOp "->"
              return psxs
            b <- term
            return $ clauseHelper ps xs b

caseExp = do _ <- reserved "case"
             ms <- caseArg `sepBy1` reservedOp "||"
             _ <- reservedOp "motive"
             mot <- caseMotive
             _ <- reserved "of"
             _ <- optional (reservedOp "|")
             cs <- clause `sepBy` reservedOp "|"
             _ <- reserved "end"
             return $ Case ms mot cs

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
                 return (c,conSigHelper as t)

alternativeArg = parens $ do
                   x <- varName
                   _ <- reservedOp ":"
                   t <- term
                   return $ DeclArg x t

emptyTypeDecl = do (tycon,tyargs) <- try $ do
                     _ <- reserved "data"
                     tycon <- decName
                     tyargs <- many typeArg
                     _ <- reserved "end"
                     return (tycon,tyargs)
                   return $ TypeDeclaration tycon tyargs []

nonEmptyTypeDecl = do (tycon,tyargs) <- try $ do
                        _ <- reserved "data"
                        tycon <- decName
                        tyargs <- many typeArg
                        _ <- reserved "where"
                        return (tycon,tyargs)
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