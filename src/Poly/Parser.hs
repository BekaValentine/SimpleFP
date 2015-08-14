module Poly.Parser where

import Control.Applicative hiding (many,(<|>),optional)
import Control.Monad (guard)
import Data.List (foldl')
import Text.ParserCombinators.Parsec

import Poly.Term
import Poly.Type
import Poly.Program



-- some useful generic parsers

--tryMulti :: Stream s m t => [ParsecT s u m a] -> ParsecT s u m a -> ParsecT s u m a
tryMulti []     d = d
tryMulti (p:ps) d = try p <|> tryMulti ps d

tok :: GenParser Char st r -> GenParser Char st r
tok p = p <* many (oneOf " \t\n")

symbol :: String -> GenParser Char st String
symbol s = tok (string s)



-- reserved keywords

reserved :: [String]
reserved = ["data", "case", "of", "end", "where", "forall"]


-- names

varName :: GenParser Char st String
varName = do res <- tok $ do c <- lower
                             cs <- many (try alphaNum <|> char '_')
                             primes <- many (char '\'')
                             return (c:cs ++ primes)
             guard $ notElem res reserved
             return $ res

decName :: GenParser Char st String
decName = do res <- tok $ do c <- upper
                             cs <- many (try alphaNum <|> char '_')
                             primes <- many (char '\'')
                             return (c:cs ++ primes)
             guard $ notElem res reserved
             return $ res


-- type parsers

typeCon :: GenParser Char st Type
typeCon = TyCon <$> decName

funType :: GenParser Char st Type
funType = do arg <- funLeft
             _ <- symbol "->"
             ret <- funRight
             return $ Fun arg ret

typeVar :: GenParser Char st Type
typeVar = TyVar <$> varName

forallType :: GenParser Char st Type
forallType = do _ <- symbol "forall"
                x <- varName
                _ <- symbol "."
                b <- forallBody
                return $ Forall x b

parenType :: GenParser Char st Type
parenType = between
              (symbol "(")
              (symbol ")")
              datatype

funLeft :: GenParser Char st Type
funLeft = tryMulti [parenType,typeCon] typeVar

funRight :: GenParser Char st Type
funRight = tryMulti [funType,parenType,forallType,typeCon] typeVar

forallBody :: GenParser Char st Type
forallBody = tryMulti [funType,parenType,forallType,typeCon] typeVar

datatype :: GenParser Char st Type
datatype = tryMulti [funType,parenType,forallType,typeCon] typeVar


-- term parsers

variable :: GenParser Char st Term
variable = do x <- varName
              return $ Var x

annotation :: GenParser Char st Term
annotation = do m <- annLeft
                _ <- symbol ":"
                t <- datatype
                return $ Ann m t

lambda :: GenParser Char st Term
lambda = do _ <- symbol "\\"
            x <- varName
            _ <- symbol "->"
            b <- lamBody
            return $ Lam x b

application :: GenParser Char st Term
application = do f <- appFun
                 a <- appArg
                 as <- many (try appArg)
                 return $ foldl' App f (a:as)

noArgConData :: GenParser Char st Term
noArgConData = do c <- decName
                  return $ Con c []

argConData :: GenParser Char st Term
argConData = do c <- decName
                as <- many1 conArg
                return $ Con c as

conData :: GenParser Char st Term
conData = try argConData <|> noArgConData

varPattern :: GenParser Char st Pattern
varPattern = VarPat <$> varName

noArgConPattern :: GenParser Char st Pattern
noArgConPattern = do c <- decName
                     return $ ConPat c []

argConPattern = do c <- decName
                   ps <- many1 argConPatternArg
                   return $ ConPat c ps

conPattern :: GenParser Char st Pattern
conPattern = try argConPattern <|> noArgConPattern

parenPattern :: GenParser Char st Pattern
parenPattern = between (symbol "(")
                       (symbol ")")
                       pattern

argConPatternArg :: GenParser Char st Pattern
argConPatternArg = tryMulti [parenPattern,noArgConPattern] varPattern

pattern :: GenParser Char st Pattern
pattern = tryMulti [parenPattern,conPattern] varPattern

clause :: GenParser Char st Clause
clause = do p <- pattern
            _ <- symbol "->"
            b <- term
            return $ Clause p b

caseExp :: GenParser Char st Term
caseExp = do _ <- symbol "case"
             m <- caseArg
             _ <- symbol "of"
             _ <- optional (symbol "|")
             cs <- clause `sepBy` symbol "|"
             _ <- symbol "end"
             return $ Case m cs

parenTerm :: GenParser Char st Term
parenTerm = between
              (symbol "(")
              (symbol ")")
              term

annLeft :: GenParser Char st Term
annLeft = tryMulti [parenTerm,conData,application] variable

lamBody :: GenParser Char st Term
lamBody = tryMulti [annotation,parenTerm,lambda,conData,caseExp,application] variable

appFun :: GenParser Char st Term
appFun = tryMulti [parenTerm] variable

appArg :: GenParser Char st Term
appArg = tryMulti [parenTerm,noArgConData] variable

conArg :: GenParser Char st Term
conArg = tryMulti [parenTerm,noArgConData] variable

caseArg :: GenParser Char st Term
caseArg = tryMulti [annotation,parenTerm,lambda,conData,application] variable

term :: GenParser Char st Term
term = tryMulti [annotation,parenTerm,lambda,conData,caseExp,application] variable

parseTerm :: String -> Either String Term
parseTerm str = case parse (spaces *> term <* eof) "(unknown)" str of
                  Left e -> Left (show e)
                  Right p -> Right p



-- program parsers

termDecl :: GenParser Char st TermDeclaration
termDecl = do _ <- symbol "let"
              x <- varName
              _ <- symbol ":"
              t <- datatype
              _ <- symbol "="
              m <- term
              _ <- symbol "end"
              return $ TermDeclaration x t m

noArgAlternative :: GenParser Char st (String,[Type])
noArgAlternative = do c <- decName
                      return $ (c,[])

argAlternative :: GenParser Char st (String,[Type])
argAlternative = do c <- decName
                    as <- many1 argAlternativeArg --datatype
                    return $ (c,as)

argAlternativeArg :: GenParser Char st Type
argAlternativeArg = try parenType <|> typeCon

alternative :: GenParser Char st (String,[Type])
alternative = try argAlternative <|> noArgAlternative

emptyTypeDecl :: GenParser Char st TypeDeclaration
emptyTypeDecl = do _ <- symbol "data"
                   tycon <- decName
                   _ <- symbol "end"
                   return $ TypeDeclaration tycon []

nonEmptyTypeDecl :: GenParser Char st TypeDeclaration
nonEmptyTypeDecl = do _ <- symbol "data"
                      tycon <- decName
                      _ <- symbol "="
                      alts <- alternative `sepBy` symbol "|"
                      _ <- symbol "end"
                      return $ TypeDeclaration tycon alts

typeDecl :: GenParser Char st TypeDeclaration
typeDecl = try nonEmptyTypeDecl
       <|> emptyTypeDecl

statement :: GenParser Char st Statement
statement = try (TmDecl <$> termDecl)
        <|> TyDecl <$> typeDecl

program :: GenParser Char st Program
program = Program <$> many1 statement



parseProgram :: String -> Either String Program
parseProgram str
  = case parse (spaces *> program <* eof) "(unknown)" str of
      Left e -> Left (show e)
      Right p -> Right p