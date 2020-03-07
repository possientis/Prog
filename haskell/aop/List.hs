{-# LANGUAGE DeriveFunctor      #-}

module  List
    (   ListC   (..)
    ,   ListS   (..)
    ,   appendC
    ,   flipAppendC
    ,   appendS
    ,   appendS2
    ,   snoc2Cons
    ,   foldC
    ,   foldS
    ,   sumC
    ,   sumS
    ,   productC
    ,   concatC
    ,   lengthC
    ,   ite
    ,   filterC
    ,   fromListC
    ,   fromListS
    ,   toListC
    ,   toListS
    ,   ex1, ex2
    ,   headC
    ,   headS
    )   where

import Nat

data ListC a 
    = NilC 
    | Cons a (ListC a)
    deriving (Functor)

data ListS a 
    = NilS 
    | Snoc (ListS a) a
    deriving (Functor)

appendC :: ListC a -> ListC a -> ListC a
appendC NilC ys = ys
appendC (Cons x xs) ys = Cons x (appendC xs ys)

appendS :: ListS a -> ListS a -> ListS a
appendS xs NilS = xs
appendS xs (Snoc ys y) = Snoc (appendS xs ys) y

snoc2Cons :: ListS a -> ListC a
snoc2Cons NilS = NilC
snoc2Cons (Snoc xs x) = appendC (snoc2Cons xs) (Cons x NilC)

foldC :: b -> (a -> b -> b) -> ListC a -> b
foldC b _ NilC = b
foldC b h (Cons x xs) = h x (foldC b h xs)

foldS :: b -> (b -> a -> b) -> ListS a -> b
foldS b _ NilS = b
foldS b h (Snoc xs x) = h (foldS b h xs) x

flipAppendC :: ListC a -> ListC a -> ListC a
flipAppendC ys = foldC ys (Cons)

appendS2 :: ListS a -> ListS a -> ListS a
appendS2 xs = foldS xs (Snoc)

sumC :: ListC Nat -> Nat
sumC = foldC zero plus'

sumS :: ListS Nat -> Nat
sumS = foldS zero plus'

productC :: ListC Nat -> Nat
productC = foldC one mult'

concatC :: ListC (ListC a) -> ListC a
concatC = foldC NilC appendC

lengthC :: ListC a -> Nat
lengthC = sumC . fmap (const one)

ite :: (a -> Bool) -> (a -> b) -> (a -> b) -> a -> b
ite p f g x = if p x then f x else g x

filterC :: (a -> Bool) -> ListC a -> ListC a
filterC p = concatC . fmap (ite p wrap nilp) where
    wrap x = Cons x NilC
    nilp _ = NilC

fromListC :: [a] -> ListC a
fromListC = foldr Cons NilC

fromListS :: [a] -> ListS a
fromListS [] = NilS
fromListS (x : xs) = appendS (Snoc NilS x) (fromListS xs)

toListC :: ListC a -> [a]
toListC = foldC [] (:)

toListS :: ListS a -> [a]
toListS NilS = []
toListS (Snoc xs x) = toListS xs ++ [x]

instance (Show a) => Show (ListC a) where
    show = show . toListC

instance (Show a) => Show (ListS a) where
    show = show . toListS

ex1 :: ListC Int
ex1 = fromListC [0,1,2,3,4,5]

ex2 :: ListS Int
ex2 = fromListS [0,1,2,3,4,5]

headC :: ListC a -> Maybe a
headC NilC = Nothing
headC (Cons x _) = Just x

headS :: ListS a -> Maybe a
headS NilS = Nothing
headS (Snoc _ x) = Just x




