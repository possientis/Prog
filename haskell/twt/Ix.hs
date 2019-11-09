{-# LANGUAGE GeneralizedNewtypeDeriving     #-}


newtype Ix m i j a = Ix
    { unsafeRunIx :: m a
    } deriving (Functor, Applicative, Monad)

