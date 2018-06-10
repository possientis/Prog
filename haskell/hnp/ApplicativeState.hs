{-# LANGUAGE DeriveFunctor #-}

newtype State s a = State { runState :: s -> (s, a) } 
    deriving Functor


instance Applicative (State s) where
    pure x = State (\s -> (s, x))
    (State ff) <*> (State fx) = State $ \s ->
        let (t,f) = ff s in
            let (u, x) = fx t in (u, f x) 




