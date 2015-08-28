module Dependent.Core.Parser where

import Control.Applicative ((<$>),(*>),(<*))
import Control.Monad (guard)
import Data.List (foldl')
import Text.Parsec
import qualified Text.Parsec.Token as Token

import Dependent.Core.Term
import Dependent.Core.Program




-- reserved keywords

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
              , Token.reservedNames = ["data","case","of","end","where","let","Type"]
              , Token.reservedOpNames = ["|","||","->","\\",":","="]
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


{-
-- type parsers

typeCon = TyCon <$> decName

funType = do arg <- try $ do
               arg <- funLeft
               _ <- reservedOp "->"
               return arg
             ret <- funRight
             return $ Fun arg ret

parenType = parens datatype

funLeft = typeCon <|> parenType

funRight = funType <|> typeCon <|> parenType

datatype = funType <|> typeCon <|> parenType
-}

-- term parsers

variable = Var <$> varName

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
             return $ Fun x arg ret

lambda = do _ <- reservedOp "\\"
            x <- varName
            _ <- reservedOp "->"
            b <- lamBody
            return $ Lam x b

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

varPattern = VarPat <$> varName

noArgConPattern = do c <- decName
                     return $ ConPat c []

conPattern = do c <- decName
                ps <- many conPatternArg
                return $ ConPat c ps

parenPattern = parens pattern

conPatternArg = parenPattern <|> noArgConPattern <|> varPattern

pattern = parenPattern <|> conPattern <|> varPattern

patternSequence = do ps <- pattern `sepBy1` reservedOp "||"
                     return $ PatternSequence ps

clause = do ps <- try $ do
              ps <- patternSequence
              _ <- reservedOp "->"
              return ps
            b <- term
            return $ Clause ps b

caseArgSequence = do ms <- caseArg `sepBy1` reservedOp "||"
                     return $ CaseArgSequence ms

caseExp = do _ <- reserved "case"
             ms <- caseArgSequence
             _ <- reserved "of"
             _ <- optional (reservedOp "|")
             cs <- clause `sepBy` reservedOp "|"
             _ <- reserved "end"
             return $ Case ms cs

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
                   return $ DeclArg (x,t)

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
            return $ DeclArg (x,t)

typeDecl = emptyTypeDecl <|> nonEmptyTypeDecl

statement = TmDecl <$> termDecl
        <|> TyDecl <$> typeDecl

program = Program <$> many statement



parseProgram :: String -> Either String Program
parseProgram str
  = case parse (spaces *> program <* eof) "(unknown)" str of
      Left e -> Left (show e)
      Right p -> Right p