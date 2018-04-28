{-# LANGUAGE RebindableSyntax #-}

import Prelude

type Vars = [(String,Nat)]

newtype Nat = Nat Integer

data Expr = Val Nat | Add Expr Expr | Var String | Random Nat


eval :: Handler StdIO e 
     => Expr 
     -> Eff e '[EXCEPTION String, STDIO, RND, STATE Vars] Nat
eval (Val x)        = return x
eval (Var x)        = do    
    vs <- get
    case lookup x vs of 
        Nothing     -> raise ("Unknown var: " ++ x) 
        Just val    -> return val
eval (Add l r)      = (+) <$> eval l <*> eval r
eval (Random max)   = do
    num <- rndNat 0 max
    putStrLn $ "Random value: " ++ show num
    retrun num


runEval :: Vars -> Expr -> IO Nat
runEval env expr = run (() :> () :> 123 :> env :> Empty) $ eval expr
