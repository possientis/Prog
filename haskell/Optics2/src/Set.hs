module  Set
    (   ex1, ex2, ex3, ex4, ex5, ex6, ex7
    )   where

import Data.Set
import Control.Lens


primes :: Set Int
primes = fromList [2,3,5,7,11,13]

ex1 :: Maybe ()
ex1 = primes ^? ix 5

ex2 :: Maybe ()
ex2 = primes ^? ix 4

ex3 :: Maybe ()
ex3 = primes ^. at 5

ex4 :: Maybe ()
ex4 = primes ^. at 4

ex5 :: Set Int
ex5 = primes & at 17 ?~ ()

ex6 :: Set Int
ex6 = sans 5 primes

ex7 :: Set Int
ex7 = primes
    & sans 5
    & sans 7
    & sans 11
