module  Nat
    (   Nat (..)
    ,   j
    ,   plus, plus', (+)
    ,   mult, mult', (*)
    ,   expn, expn', (^)
    ,   fact, fact2, fact3
    ,   fib, fib2
    ,   foldn
    ,   zero, one
    )   where

import qualified Prelude as P
import Prelude hiding 
    (   (+)
    ,   (*)
    ,   (^)
    ,   toInteger
    )

data Nat = Zero | Succ Nat

toInteger :: Nat -> Integer
toInteger Zero     = 0
toInteger (Succ n) = 1 P.+ toInteger n

j :: Integer -> Nat
j 0 = Zero
j n = Succ (j (n - 1))

instance Show Nat where
    show = show . toInteger

zero :: Nat
zero = Zero

one :: Nat
one = Succ Zero

plus :: (Nat, Nat) -> Nat
plus (m, Zero)   = m
plus (m, Succ n) = Succ $ plus (m,n)

mult :: (Nat, Nat) -> Nat
mult (_, Zero)   = Zero
mult (m, Succ n) = plus (m, mult (m,n))

expn :: (Nat, Nat) -> Nat
expn (_, Zero)  = one
expn (m, Succ n) = mult (m, expn (m,n)) 

(+) :: Nat -> Nat -> Nat 
(+) m n = plus (m,n)

(*) :: Nat -> Nat -> Nat
(*) m n = mult (m,n)

(^) :: Nat -> Nat -> Nat
(^) m n = expn (m,n)

fact :: Nat -> Nat
fact Zero     = one
fact (Succ n) = (Succ n) *  fact n

fib :: Nat -> Nat
fib Zero            = zero
fib (Succ Zero)     = one
fib (Succ (Succ n)) = fib n + fib (Succ n)

foldn :: (a,a->a) -> Nat -> a
foldn (c,_) Zero     = c
foldn (c,h) (Succ n) = h (foldn (c,h) n) 

plus' :: Nat -> Nat -> Nat
plus' m = foldn (m, Succ)

mult' :: Nat -> Nat -> Nat
mult' m = foldn (Zero, plus' m)

expn' :: Nat -> Nat -> Nat
expn' m = foldn (one, mult' m)

fact2 :: Nat -> Nat
fact2 = go one where
    go acc Zero     = acc
    go acc (Succ n) = go (Succ n * acc) n

fact3 :: Nat -> Nat
fact3 = fst . foldn ((one, one), f) where
    f :: (Nat, Nat) -> (Nat, Nat) 
    f (p,q) = (p*q, q + one)

fib2 :: Nat -> Nat
fib2 = snd . foldn ((one,zero), f) where
    f :: (Nat, Nat) -> (Nat, Nat)
    f (p, q) = (q, p + q)

