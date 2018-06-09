{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

newtype Backwards f a = Backwards { forwards :: f a }

deriving instance (Functor f ) => Functor (Backwards f) 


instance (Applicative f) => Applicative (Backwards f) where
    pure = Backwards . pure
    (Backwards ff) <*> (Backwards fx) = ... 

