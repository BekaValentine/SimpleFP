{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Record.Core.Parser where
import System.IO.Unsafe
import Control.Applicative ((<$>),(<*>),(*>),(<*))
import Control.Monad.Reader
import Data.List (foldl')
import Text.Parsec
import qualified Text.Parsec.Token as Token

import Abs
import Plicity
import Scope
import Record.Core.Abstraction
import Record.Core.ConSig
import Record.Core.Term
import Record.Core.Program




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
              , Token.reservedNames = ["data","case","motive","of","end","where"
                                      ,"let","Type","module","open","opening"
                                      ,"as","using","hiding","renaming","to","in","Rec"]
              , Token.reservedOpNames = ["|","||","->","\\",":","::","=",".",","]
              , Token.caseSensitive = True
              }

tokenParser = Token.makeTokenParser languageDef

identifier = Token.identifier tokenParser
reserved = Token.reserved tokenParser
reservedOp = Token.reservedOp tokenParser
parens = Token.parens tokenParser
braces = Token.braces tokenParser
symbol = Token.symbol tokenParser





-- names

varName = do lookAhead lower
             identifier

decName = do lookAhead upper
             identifier


-- open settings

oAs = optionMaybe $ do
        _ <- reserved "as"
        decName

oHidingUsing = optionMaybe (hiding <|> using)
  where
    hiding = do _ <- reserved "hiding"
                ns <- parens (sepBy (varName <|> decName) (reservedOp ","))
                return (Hiding ns)
    using = do _ <- reserved "using"
               ns <- parens (sepBy (varName <|> decName) (reservedOp ","))
               return (Using ns)

oRenaming = do m <- openRenamingP
               case m of
                 Nothing -> return []
                 Just ns -> return ns
  where
    openRenamingP = optionMaybe $ do
                      _ <- reserved "renaming"
                      parens (sepBy (varRen <|> decRen) (reservedOp ","))
    varRen = do n <- varName
                _ <- reserved "to"
                n' <- varName
                return (n,n')
    decRen = do n <- decName
                _ <- reserved "to"
                n' <- decName
                return (n,n')

openSettings = OpenSettings <$> decName
                            <*> oAs
                            <*> oHidingUsing
                            <*> oRenaming


-- term parsers

variable = Var <$> (Name <$> varName)


dottedVar = try $ do
              modName <- decName
              _ <- reservedOp "."
              valName <- varName
              return $ DottedVar modName valName


recordDot = do (m,f) <- try $ do
                 m <- recDotArg
                 _ <- reservedOp "."
                 f <- varName
                 return (m,f)
               fieldNames <- many $ do
                 _ <- reservedOp "."
                 varName
               return $ foldl' RecordDot m (f:fieldNames)

recDotArg = recordType <|> recordCon <|> dottedVar <|> variable <|> parenTerm <|> typeType

dottedThings = recordDot <|> dottedVar

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

bareCon = BareCon <$> decName

dottedCon = try $ do
              modName <- decName
              _ <- reservedOp "."
              conName <- decName
              return $ DottedCon modName conName

constructor = dottedCon <|> bareCon

noArgConData = do c <- constructor
                  return $ Con c []

conData = do c <- constructor
             as <- many conArg
             return $ Con c as

assertionPattern = do _ <- reservedOp "."
                      m <- assertionPatternArg
                      return $ (AssertionPat m, [])

varPattern = do x <- varName
                return (VarPat x,[x])

noArgConPattern = do c <- constructor
                     return $ (ConPat c PatternSeqNil, [])

conPattern = do c <- constructor
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

openExp = do _ <- reserved "open"
             _ <- optional (reserved "|")
             settings <- sepBy openSettings (reserved "|")
             _ <- reserved "in"
             m <- term
             _ <- reserved "end"
             return (OpenIn settings m)

recordType = do _ <- reserved "Rec"
                xts <- braces $ fieldDecl `sepBy` reservedOp ","
                return $ RecordType (telescopeHelper xts)
  where
    fieldDecl = do x <- varName
                   _ <- reservedOp ":"
                   t <- term
                   return (x,t)

emptyRecordCon = try $ do
                   braces $ return ()
                   return $ RecordCon []

nonEmptyRecordCon = do x <- try $ do
                         _ <- symbol "{"
                         x <- varName
                         _ <- reservedOp "="
                         return x
                       m <- term
                       xms' <- many $ do
                         _ <- reservedOp ","
                         x' <- varName
                         _ <- reservedOp "="
                         m' <- term
                         return (x',m')
                       _ <- symbol "}"
                       return $ RecordCon ((x,m):xms')

recordCon = emptyRecordCon <|> nonEmptyRecordCon
                       

parenTerm = parens term

annLeft = application <|> dottedThings <|> parenTerm <|> conData <|> variable <|> typeType <|> recordType <|> recordCon

annRight = application <|> dottedThings <|> funType <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType <|> recordType <|> recordCon

funArg = annotation <|> funType <|> application <|> dottedThings <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType <|> openExp <|> recordType <|> recordCon

funRet = annotation <|> funType <|> application <|> dottedThings <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType <|> openExp <|> recordType <|> recordCon

lamBody = annotation <|> funType <|> application <|> dottedThings <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType <|> openExp <|> recordType <|> recordCon

appFun = dottedThings <|> parenTerm <|> variable <|> typeType <|> recordType <|> recordCon

rawExplAppArg = dottedThings <|> parenTerm <|> noArgConData <|> variable <|> typeType <|> recordType <|> recordCon

explAppArg = do m <- rawExplAppArg
                return (Expl,m)

rawImplAppArg = annotation <|> funType <|> application <|> dottedThings <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType <|> openExp <|> recordType <|> recordCon

implAppArg = do m <- braces $ rawImplAppArg
                return (Impl,m)

appArg = explAppArg <|> implAppArg

rawExplConArg = dottedThings <|> parenTerm <|> noArgConData <|> variable <|> typeType <|> recordType <|> recordCon

explConArg = do m <- rawExplConArg
                return (Expl,m)

rawImplConArg = annotation <|> funType <|> application <|> dottedThings <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType <|> openExp <|> recordType <|> recordCon

implConArg = do m <- braces $ rawImplConArg
                return (Impl,m)

conArg = explConArg <|> implConArg

caseArg = annotation <|> funType <|> application <|> dottedThings <|> parenTerm <|> lambda <|> conData <|> variable <|> typeType <|> recordType <|> recordCon

term = annotation <|> funType <|> application <|> dottedThings <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType <|> openExp <|> recordType <|> recordCon

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

modulOpen = do n <- try $ do
                 _ <- reserved "module"
                 n <- decName
                 _ <- reserved "opening"
                 return n
               _ <- optional (reserved "|")
               settings <- sepBy openSettings (reserved "|")
               _ <- reserved "where"
               stmts <- many statement
               _ <- reserved "end"
               return $ Module n settings stmts

modulNoOpen = do n <- try $ do
                   _ <- reserved "module"
                   n <- decName
                   _ <- reserved "where"
                   return n
                 stmts <- many statement
                 _ <- reserved "end"
                 return $ Module n [] stmts

modul = modulOpen <|> modulNoOpen

program = Program <$> many modul



parseProgram :: String -> Either String Program
parseProgram str
  = case parse (spaces *> program <* eof) "(unknown)" str of
      Left e -> Left (show e)
      Right p -> Right p