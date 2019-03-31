module  TI
    (   TI  (..)
    )   where

import Subst

-- The 'TI' (Type Inference) monad is a state monad where the state
-- is simply a substitution (the current substitution) and an integer
-- (needed for generating fresh variables)

newtype TI a = TI { runTI :: Subst -> Int -> (Subst, Int, a) }



instance Functor TI where
    fmap f m = TI $ \s i -> let (s',i',a) = runTI m s i  in (s',i',f a)

instance Applicative TI where
    pure      = return
    (<*>) g m = g >>= \f -> fmap f m 

instance Monad TI where
    return a  = TI $ \s i -> (s, i, a) 
    m >>= f   = TI $ \s i -> let (s',i',a) = runTI m s i in runTI (f a) s' i'


