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

