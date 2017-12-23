{-# LANGUAGE ExplicitForAll #-}

import Data.Void
import Data.Text


data Foo tag a = Foo a

combine :: Num a => Foo tag a -> Foo tag a -> Foo tag a
combine (Foo a) (Foo b) = Foo (a + b)

-- all identical at the value level, but differ at type level.

a :: Foo () Int
a = Foo 1

b :: Foo t Int
b = Foo 1

b' :: forall t. Foo t Int
b' = Foo 1

c :: Foo Void Int
c = Foo 1


-- () ~ ()
ex1 :: Foo () Int
ex1 = combine a a 


-- t ~ ()
ex2 :: Foo () Int
ex2 = combine a b

-- t0 ~ t1
ex3 :: Foo t Int
ex3 = combine b b 

-- t ~ Void
ex4 :: Foo Void Int
ex4 = combine b c

{-
-- cannot match t and Void
ex5 :: Foo t Int
ex5 = combine b c

-}

data Key -- some type

newtype Plaintext = Plaintext Text
newtype Cryptotext = Cryptotext Text

encrypt :: Key -> Plaintext -> Cryptotext
encrypt = undefined

decrypt :: Key -> Cryptotext -> Plaintext
decrypt = undefined

-- different API using phantom types

data Cryptotext'
data Plaintext'

data Msg a = Msg Text

encrypt' :: Key -> Msg Plaintext -> Msg Cryptotext
encrypt' = undefined

decrypt' :: Key -> Msg Cryptotext -> Msg Plaintext
decrypt' = undefined


data Token a    -- void type with phantom type




