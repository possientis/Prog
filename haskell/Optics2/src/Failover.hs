module  Failover
    (   failover
    ,   failing
    ,   ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8, ex9, ex10
    ,   ex11
    )   where

import Data.Map
import Data.Char
import Data.Monoid
import Control.Applicative

import Control.Lens hiding (failover, failing)
import qualified Control.Lens as L (failover, failing)
--
-- Actual signature
failover :: Alternative m => LensLike ((,) Any) s t a b -> (a -> b) -> s -> m t
failover = undefined

-- specialized
-- failover :: Traversal s t a b -> (a -> b) -> s -> Maybe t

-- actual signature
failing :: (Conjoined p, Applicative f) 
        => Traversing p f s t a b
        -> Over p f s t a b
        -> Over p f s t a b
failing = undefined

--specialized
-- failing :: Fold s t a b -> Fold s t a b -> Fold s t a b 
-- failing :: Traversal s t a b -> Traversal s t a b -> Traversal s t a b

ex1 :: Maybe String
ex1 = "abcd" & L.failover (ix 6) toUpper

ex2 :: Maybe String
ex2 = "abcd" & L.failover (ix 2) toUpper

ex3 :: IO String
ex3 = "abcd" & L.failover (ix 6) toUpper

ex4 :: Maybe [Int]
ex4 = [] & L.failover _head (*10)

ex5 :: Maybe [Int]
ex5 = [1,3,5] & L.failover (traversed . filtered even) (*10)

ex6 :: Maybe [Int]
ex6 = [1,4,5] & L.failover (traversed . filtered even) (*10)

ex7 :: String
ex7 = "abcdefg"

ex8 :: Maybe Int
ex8 = fromList [('a',1),('b',2)] ^? (ix 'z' `L.failing` ix 'b')

ex9 :: Map Char Int
ex9 = fromList [('a',1),('b',2)] & (ix 'z' `L.failing` ix 'b') *~ 10

ex10 :: Maybe String
ex10 = fromList [("Bieber","Believe"),("Beyonce","Lemonade")]
     ^? (ix "Swiftt" `L.failing` ix "Bieber" `L.failing` ix "Beyonce")

ex11 :: [Int]
ex11 = fromList [('a',(1,[2,3,4])),('b',(5,[6,7,8]))]
    ^.. (ix 'z' . _1
        `L.failing` ix 'a' . _2 . ix 10
        `L.failing` ix 'b' . _2 . traversed
        )
