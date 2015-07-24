module Monadic.REPL where

import System.IO

import Monadic.Elaboration
import Monadic.TypeChecking
import Core.Evaluation
import Core.Parser

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
             Right (sig,ctx,env)
               -> do hSetBuffering stdin LineBuffering
                     until_ (== ":quit")
                            (readPrompt "$> ")
                            (evalAndPrint sig ctx env)
  where
    loadProgram :: String -> Either String (Signature,Context,Env)
    loadProgram src
      = do prog <- parseProgram src
           (sig,ctx) <- runElaborator (elabProgram prog)
           env <- contextToEnv ctx
           return (sig,ctx,env)
    
    loadTerm :: Signature -> Context -> Env -> String -> Either String Value
    loadTerm sig ctx env src
      = do tm <- parseTerm src
           case runTypeChecker (infer tm) sig ctx of
             Nothing -> Left "Unable to infer type."
             Just _ -> eval env tm
    
    evalAndPrint :: Signature -> Context -> Env -> String -> IO ()
    evalAndPrint _ _ _ "" = return ()
    evalAndPrint sig ctx env src
      = case loadTerm sig ctx env src of
          Left e -> flushStr (e ++ "\n")
          Right v -> flushStr (show v ++ "\n")

replFile :: String -> IO ()
replFile loc = readFile loc >>= repl