module Simple.Core.Evaluation where

import Data.List (intercalate)

import Simple.Core.Term


-- Evaluation Environments

type Env = [(String,Value)]

lookupEnv :: String -> Env -> Maybe Value
lookupEnv = lookup



-- Values

data Value
  = Clo Env String Term
  | ConVal String [Value]

data ValueParenLoc = RootValue | CloBody | ConValArg
  deriving (Eq)

instance Show Value where
  show t = aux RootValue t
    where
      aux c t
        = let (cs,str) = case t of
                Clo _ x b   -> ([RootValue,CloBody], "\\" ++ x ++ " -> " ++ show b)
                ConVal c [] -> ([RootValue,CloBody,ConValArg], c)
                ConVal c as -> ([RootValue,CloBody], c ++ " " ++ intercalate " " (map (aux ConValArg) as))
          in if c `elem` cs
             then str
             else "(" ++ str ++ ")"



-- Pattern Matching

match :: Pattern -> Value -> Maybe Env
match (VarPat x) v = Just [(x,v)]
match (ConPat c ps) (ConVal c' as) | c == c' && length ps == length as
  = fmap concat (sequence (zipWith match ps as))
match _ _ = Nothing

matchClauses :: [Clause] -> Value -> Maybe (Env,Term)
matchClauses []              _ = Nothing
matchClauses (Clause p b:cs) v = case match p v of
                                   Nothing   -> matchClauses cs v
                                   Just env' -> Just (env',b)



-- Standard Eager Evaluation

eval :: Env -> Term -> Either String Value
eval env (Var x)        = case lookupEnv x env of
                            Nothing -> Left ("Unbound variable: " ++ x ++ "\nEnvironment: " ++ show env)
                            Just m  -> return m
eval env (Ann m _)      = eval env m
eval env (Lam x b)      = return $ Clo env x b
eval env (App f a)      = do ef <- eval env f
                             ea <- eval env a
                             case (ef, ea) of
                               (Clo env' x b, a') -> eval ((x,a'):env') b
                               (f',_)             -> Left $ "Cannot apply a non-function: " ++ show f'
eval env (Con c as)     = do eas <- sequence (map (eval env) as)
                             return $ ConVal c eas
eval env (Case m cs)    = do em <- eval env m
                             case matchClauses cs em of
                               Nothing        -> Left $ "Incomplete pattern match: " ++ show (Case m cs)
                               Just (env', b) -> eval (env'++env) b