module Core.Parser where

import Control.Applicative hiding (many,(<|>),optional)
import Control.Monad (guard)
import Data.List (foldl')
import Text.ParserCombinators.Parsec

import Core.Term
import Core.Type
import Core.Program



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
reserved = ["data", "case", "of", "end", "where"]



-- type parsers

typeCon :: GenParser Char st Type
typeCon = TyCon <$> decName

funType :: GenParser Char st Type
funType = do arg <- funLeft
             _ <- symbol "->"
             ret <- funRight
             return $ Fun arg ret

parenType :: GenParser Char st Type
parenType = between
              (symbol "(")
              (symbol ")")
              datatype

funLeft :: GenParser Char st Type
funLeft = try typeCon
      <|> parenType

funRight :: GenParser Char st Type
funRight = tryMulti [funType,typeCon] parenType

datatype :: GenParser Char st Type
datatype = tryMulti [funType,typeCon] parenType


-- term parsers

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

conData :: GenParser Char st Term
conData = do c <- decName
             as <- between
                     (symbol "(")
                     (symbol ")")
                     (conArg `sepBy` symbol ",")
             return $ Con c as

varPattern :: GenParser Char st Pattern
varPattern = VarPat <$> varName

conPattern :: GenParser Char st Pattern
conPattern = do c <- decName
                ps <- between
                        (symbol "(")
                        (symbol ")")
                        (pattern `sepBy` symbol ",")
                return $ ConPat c ps

pattern :: GenParser Char st Pattern
pattern = try conPattern
      <|> varPattern

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
lamBody = tryMulti [parenTerm,lambda,conData,caseExp,{-annotation,-}application] variable

appFun :: GenParser Char st Term
appFun = tryMulti [parenTerm] variable

appArg :: GenParser Char st Term
appArg = tryMulti [parenTerm] variable

conArg :: GenParser Char st Term
conArg = tryMulti [parenTerm,lambda,conData,caseExp,{-annotation,-}application] variable

caseArg :: GenParser Char st Term
caseArg = tryMulti [parenTerm,lambda,conData,{-annotation,-}application] variable

term :: GenParser Char st Term
term = tryMulti [parenTerm,lambda,conData,caseExp,{-annotation,-}application] variable

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

alternative :: GenParser Char st (String,[Type])
alternative = do c <- decName
                 as <- between
                         (symbol "(")
                         (symbol ")")
                         (datatype `sepBy` symbol ",")
                 return $ (c,as)

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