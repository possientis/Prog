{-# LANGUAGE GADTs #-}

data StateI s a where
    Get :: StateI s s
    Put :: s -> StateI s ()


data Freer i a where
    Return :: a   -> Freer i a
    (:>>=) :: i a -> (a -> Freer i b) -> Freer i b 
