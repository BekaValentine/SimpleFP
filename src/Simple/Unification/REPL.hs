module Simple.Unification.REPL where

import Control.Monad.Reader
import System.IO

import Env
import Eval
import Simple.Unification.Elaboration
import Simple.Unification.TypeChecking
import Simple.Core.Evaluation
import Simple.Core.Parser
import Simple.Core.Term

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
             Left e -> flushStr ("ERROR: " ++ e ++ "\n")
             Right (sig,defs,ctx,i,env)
               -> do hSetBuffering stdin LineBuffering
                     until_ (== ":quit")
                            (readPrompt "$> ")
                            (evalAndPrint sig defs ctx i env)
  where
    loadProgram :: String -> Either String (Signature,Definitions,Context,Int,Environment String Term)
    loadProgram src
      = do prog <- parseProgram src
           ElabState sig defs ctx i <- runElaborator (elabProgram prog)
           let env = [ (x,m) | (x,m,_) <- defs ]
           return (sig,defs,ctx,i,env)
    
    loadTerm :: Signature -> Definitions -> Context -> Int -> Environment String Term -> String -> Either String Term
    loadTerm sig defs ctx i env src
      = do tm <- parseTerm src
           case runTypeChecker (infer tm) sig defs ctx i of
             Left e  -> Left e
             Right _ -> runReaderT (eval tm) env
    
    evalAndPrint :: Signature -> Definitions -> Context -> Int -> Environment String Term -> String -> IO ()
    evalAndPrint _ _ _ _ _ "" = return ()
    evalAndPrint sig defs ctx i env src
      = case loadTerm sig defs ctx i env src of
          Left e  -> flushStr ("ERROR: " ++ e ++ "\n")
          Right v -> flushStr (show v ++ "\n")

replFile :: String -> IO ()
replFile loc = readFile loc >>= repl