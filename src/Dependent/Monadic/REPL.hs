module Dependent.Monadic.REPL where

import Control.Monad.Reader (runReaderT)
import System.IO

import Env
import Eval
import Dependent.Core.ConSig
import Dependent.Core.Evaluation
import Dependent.Core.Parser
import Dependent.Core.Term
import Dependent.Monadic.Elaboration
import Dependent.Monadic.TypeChecking



flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ p prompt action = do 
   result <- prompt
   if p result 
      then return ()
      else action result >> until_ p prompt action

repl :: String -> IO ()
repl src = case loadProgram src of
             Left e -> flushStr e
             Right (sig,defs,ctx,env)
               -> do hSetBuffering stdin LineBuffering
                     until_ (== ":quit")
                            (readPrompt "$> ")
                            (evalAndPrint sig defs ctx env)
  where
    loadProgram :: String -> Either String (Signature Term,Definitions,Context,Environment String Term)
    loadProgram src
      = do prog <- parseProgram src
           ElabState sig defs ctx <- runElaborator (elabProgram prog)
           let env = definitionsToEnvironment defs
           return (sig,defs,ctx,env)
    
    loadTerm :: Signature Term -> Definitions -> Context -> Environment String Term -> String -> Either String Term
    loadTerm sig defs ctx env src
      = do tm <- parseTerm src
           case runTypeChecker (infer tm) sig defs ctx of
             Nothing -> Left "Unable to infer type."
             Just _ -> runReaderT (eval tm) env
    
    evalAndPrint :: Signature Term -> Definitions -> Context -> Environment String Term -> String -> IO ()
    evalAndPrint _ _ _ _ "" = return ()
    evalAndPrint sig defs ctx env src
      = case loadTerm sig defs ctx env src of
          Left e -> flushStr (e ++ "\n")
          Right v -> flushStr (show v ++ "\n")

replFile :: String -> IO ()
replFile loc = readFile loc >>= repl