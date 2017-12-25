{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}

import GHC.TypeLits
import Data.Type.Equality


type Not a b = ((b == a) ~ False)

restrictUnit :: Not () a => a -> a
restrictUnit = id

{-
ex1 :: ()
ex1 = restrictUnit () -- compile error
-}

ex2 :: Int
ex2 = restrictUnit 34


restrictChar :: Not Char a => a -> a
restrictChar = id

{-
ex3 :: Char
ex3 = restrictChar 'a' -- compile error
-}

ex4 :: Int
ex4 = restrictChar 46
