{-# LANGUAGE GeneralizedNewtypeDeriving #-}

newtype ZipList a = ZipList { getZipList :: [a] } deriving Functor


instance Applicative ZipList where
    pure x = ZipList (repeat x) -- repeat ?


