{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

data Size = Empty | NonEmpty

data List b a where
    Nil  :: List Empty a
    Cons :: a -> List b a -> List NonEmpty a


head' :: List NonEmpty a -> a
head' (Cons x _) = x


ex1 :: Int
ex1 = head' (1 `Cons` (2 `Cons` Nil))

-- Compiler error
--ex2 :: Int
--ex2 = head' Nil



    
