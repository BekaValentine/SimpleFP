{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module DependentImplicit.Core.Parser where

import Control.Applicative ((<$>),(<*>),(*>),(<*))
import Control.Monad.Reader
import Data.List (foldl')
import Text.Parsec
import qualified Text.Parsec.Token as Token

import Abs
import Plicity
import Scope
import DependentImplicit.Core.Abstraction
import DependentImplicit.Core.ConSig
import DependentImplicit.Core.Term
import DependentImplicit.Core.Program




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
braces = Token.braces tokenParser





-- names

varName = do lookAhead (lower <|> char '_')
             identifier

decName = do lookAhead upper
             identifier


-- term parsers

variable = do x <- varName
              guard (x /= "_")
              return $ Var (Name x)

annotation = do m <- try $ do
                  m <- annLeft
                  _ <- reservedOp ":"
                  return m
                t <- annRight
                return $ Ann m t

typeType = do _ <- reserved "Type"
              return Type

explFunType = do (x,arg) <- try $ do
                              (x,arg) <- parens $ do
                                x <- varName
                                _ <- reservedOp ":"
                                arg <- funArg
                                return (x,arg)
                              _ <- reservedOp "->"
                              return (x,arg)
                 ret <- funRet
                 return $ funHelper Expl x arg ret

implFunType = do (x,arg) <- try $ do
                              (x,arg) <- braces $ do
                                x <- varName
                                _ <- reservedOp ":"
                                arg <- funArg
                                return (x,arg)
                              _ <- reservedOp "->"
                              return (x,arg)
                 ret <- funRet
                 return $ funHelper Impl x arg ret

funType = explFunType <|> implFunType

explLambda = do x <- try $ do
                  _ <- reservedOp "\\"
                  varName
                _ <- reservedOp "->"
                b <- lamBody
                return $ lamHelper Expl x b

implLambda = do x <- try $ do
                  _ <- reservedOp "\\"
                  braces varName
                _ <- reservedOp "->"
                b <- lamBody
                return $ lamHelper Impl x b

lambda = explLambda <|> implLambda

application = do (f,pa) <- try $ do
                   f <- appFun
                   pa <- appArg
                   return (f,pa)
                 pas <- many appArg
                 return $ foldl' (\f' (plic,a') -> App plic f' a') f (pa:pas)

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
    patternSeqAndNames :: [(Plicity,(Pattern,[String]))] -> (PatternSeq,[String])
    patternSeqAndNames []
      = (PatternSeqNil, [])
    patternSeqAndNames ((plic,(p,xs)):psxs)
      = let (ps,xs') = patternSeqAndNames psxs
        in (patternSeqHelper plic p xs ps, xs++xs')

parenPattern = parens pattern

rawExplConPatternArg = assertionPattern <|> parenPattern <|> noArgConPattern <|> varPattern

explConPatternArg = do p <- rawExplConPatternArg
                       return (Expl,p)

rawImplConPatternArg = assertionPattern <|> parenPattern <|> conPattern <|> varPattern

implConPatternArg = do p <- braces $ rawImplConPatternArg
                       return (Impl,p)

conPatternArg = explConPatternArg <|> implConPatternArg

assertionPatternArg = parenTerm <|> noArgConData <|> variable <|> typeType

pattern = assertionPattern <|> parenPattern <|> conPattern <|> varPattern

patternSeqConsNil = do (p,xs) <- pattern
                       return (PatternSeqCons Expl p (scope xs PatternSeqNil), xs)

patternSeqCons = do (p,xs) <- try $ do
                      pxs <- pattern
                      _ <- reservedOp "||"
                      return pxs
                    (ps,xs') <- patternSeq
                    return (patternSeqHelper Expl p xs ps,xs++xs')

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

rawExplAppArg = parenTerm <|> noArgConData <|> variable <|> typeType

explAppArg = do m <- rawExplAppArg
                return (Expl,m)

rawImplAppArg = annotation <|> funType <|> application <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType

implAppArg = do m <- braces $ rawImplAppArg
                return (Impl,m)

appArg = explAppArg <|> implAppArg

rawExplConArg = parenTerm <|> noArgConData <|> variable <|> typeType

explConArg = do m <- rawExplConArg
                return (Expl,m)

rawImplConArg = annotation <|> funType <|> application <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType

implConArg = do m <- braces $ rawImplConArg
                return (Impl,m)

conArg = explConArg <|> implConArg

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

explAlternativeArg = parens $ do
                       x <- varName
                       _ <- reservedOp ":"
                       t <- term
                       return $ DeclArg Expl x t

implAlternativeArg = braces $ do
                       x <- varName
                       _ <- reservedOp ":"
                       t <- term
                       return $ DeclArg Impl x t

alternativeArg = explAlternativeArg <|> implAlternativeArg

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

explTypeArg = parens $ do
                x <- varName
                _ <- reservedOp ":"
                t <- term
                return $ DeclArg Expl x t

implTypeArg = braces $ do
                x <- varName
                _ <- reservedOp ":"
                t <- term
                return $ DeclArg Impl x t

typeArg = explTypeArg <|> implTypeArg

typeDecl = emptyTypeDecl <|> nonEmptyTypeDecl

statement = TmDecl <$> termDecl
        <|> TyDecl <$> typeDecl

program = Program <$> many statement



parseProgram :: String -> Either String Program
parseProgram str
  = case parse (spaces *> program <* eof) "(unknown)" str of
      Left e -> Left (show e)
      Right p -> Right p