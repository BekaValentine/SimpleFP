module Poly.Parser where

import Control.Applicative ((<$>),(*>),(<*),(<*>))
import Control.Monad (guard)
import Data.List (foldl')
import Text.Parsec
import qualified Text.Parsec.Token as Token

import Poly.Term
import Poly.Type
import Poly.Program




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
              , Token.reservedNames = ["data","case","of","end","where","let","forall"]
              , Token.reservedOpNames = ["|","->","\\",":","=","."]
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


-- type parsers

noArgTypeCon = do c <- decName
                  return $ TyCon c []

typeCon = TyCon <$> decName <*> many tyConArg

funType = do arg <- try $ do
               arg <- funLeft
               _ <- reservedOp "->"
               return arg
             ret <- funRight
             return $ Fun arg ret

typeVar = TyVar <$> varName

forallType = do _ <- reserved "forall"
                x <- varName
                _ <- reservedOp "."
                b <- forallBody
                return $ Forall x b

parenType = parens datatype

tyConArg = parenType <|> noArgTypeCon <|> typeVar

funLeft = parenType <|> typeCon <|> typeVar

funRight = funType <|> parenType <|> forallType <|> typeCon <|> typeVar

forallBody = funType <|> parenType <|> forallType <|> typeCon <|> typeVar

datatype = funType <|> parenType <|> forallType <|> typeCon <|> typeVar


-- term parsers

variable = Var <$> varName

annotation = do m <- try $ do
                  m <- annLeft
                  _ <- reservedOp ":"
                  return m
                t <- datatype
                return $ Ann m t

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

clause = do p <- try $ do
              p <- pattern
              _ <- reservedOp "->"
              return p
            b <- term
            return $ Clause p b

caseExp = do _ <- reserved "case"
             m <- caseArg
             _ <- reserved "of"
             _ <- optional (reservedOp "|")
             cs <- clause `sepBy` reservedOp "|"
             _ <- reserved "end"
             return $ Case m cs

parenTerm = parens term

annLeft = application <|> parenTerm <|> conData <|> variable

lamBody = annotation <|> application <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable

appFun = parenTerm <|> variable

appArg = parenTerm <|> noArgConData <|> variable

conArg = parenTerm <|> noArgConData <|> variable

caseArg = annotation <|> application <|> parenTerm <|> lambda <|> conData <|> variable

term = annotation <|> application <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable

parseTerm str = case parse (spaces *> term <* eof) "(unknown)" str of
                  Left e -> Left (show e)
                  Right p -> Right p



-- program parsers

termDecl = do _ <- reserved "let"
              x <- varName
              _ <- reservedOp ":"
              t <- datatype
              _ <- reservedOp "="
              m <- term
              _ <- reserved "end"
              return $ TermDeclaration x t m

alternative = do c <- decName
                 as <- many alternativeArg
                 return (c,as)

alternativeArg = parenType <|> typeCon <|> typeVar

typeDecl = do _ <- reserved "data"
              tycon <- decName
              params <- many varName
              alts <- option [] $ do
                _ <- reservedOp "="
                alternative `sepBy` reservedOp "|"
              _ <- reserved "end"
              return $ TypeDeclaration tycon params alts

statement = TmDecl <$> termDecl
        <|> TyDecl <$> typeDecl

program = Program <$> many statement



parseProgram :: String -> Either String Program
parseProgram str
  = case parse (spaces *> program <* eof) "(unknown)" str of
      Left e -> Left (show e)
      Right p -> Right p