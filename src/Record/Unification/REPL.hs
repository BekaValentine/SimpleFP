module Record.Unification.REPL where

import Control.Monad.Reader (runReaderT)
import System.IO

import Env
import Eval
import Record.Core.ConSig
import Record.Core.Evaluation
import Record.Core.Parser
import Record.Core.Term
import Record.Unification.Elaboration
import Record.Unification.TypeChecking



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
             Right (sig,defs,ctx,i,env,ms)
               -> do hSetBuffering stdin LineBuffering
                     until_ (== ":quit")
                            (readPrompt "$> ")
                            (evalAndPrint sig defs ctx i env ms)
  where
    loadProgram :: String -> Either String (Signature Term,Definitions,Context,Int,Environment (String,String) Term,[String])
    loadProgram src
      = do prog <- parseProgram src
           ElabState sig defs ctx i _ _ ms <- runElaborator (elabProgram prog)
           let env = [ (x,m) | (x,m,_) <- defs ]
           return (sig,defs,ctx,i,env,ms)
    
    loadTerm :: Signature Term -> Definitions -> Context -> Int -> Environment (String,String) Term -> [String] -> String -> Either String Term
    loadTerm sig defs ctx i env ms src
      = do tm <- parseTerm src
           case runTypeChecker (infer tm) sig defs ctx i ([ (Right p,p) | (p,_) <- sig ] ++ [ (Right p,p) | (p,_,_) <- defs ]) ms of
             Left e  -> Left e
             Right ((tm',_),_) -> runReaderT (eval tm') env
    
    evalAndPrint :: Signature Term -> Definitions -> Context -> Int -> Environment (String,String) Term -> [String] -> String -> IO ()
    evalAndPrint _ _ _ _ _ _ "" = return ()
    evalAndPrint sig defs ctx i env ms src
      = case loadTerm sig defs ctx i env ms src of
          Left e  -> flushStr ("ERROR: " ++ e ++ "\n")
          Right v -> flushStr (show v ++ "\n")

replFile :: String -> IO ()
replFile loc = readFile loc >>= repl