{-# LANGUAGE DeriveFunctor      #-}

data List a = Nil | Cons a (List a)
    deriving (Functor)

-- some implementation of traverse
traverse1 :: (Applicative f) => (a -> f b) -> List a -> f (List b)
traverse1 _ Nil = pure Nil
traverse1 f (Cons x xs) = Cons <$> (f x) <*> (traverse1 f xs)  

-- some implementation of sequenceA
sequenceA1 :: (Applicative f) => List (f a) -> f (List a)
sequenceA1 Nil = pure Nil
sequenceA1 (Cons x xs) = Cons <$> x <*> sequenceA1 xs

-- traverse can be implemented in terms of sequenceA
traverse2 :: (Applicative f) => (a -> f b) -> List a -> f (List b)
traverse2 = (.) sequenceA1 . fmap

-- sequenceA can be implemented in terms of traverse
sequenceA2 :: (Applicative f) => List (f a) -> f (List a)
sequenceA2 = traverse1 id

-- MapM is just the same as traverse for monadic actions
mapM1 :: (Monad m) => (a -> m b) -> List a -> m (List b)
mapM1 = traverse1

-- sequence is just sequenceA for lists of mandic actions
sequence1 :: (Monad m) => List (m a) -> m (List a)
sequence1 = sequenceA1 
