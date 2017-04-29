{-# LANGUAGE GeneralizedNewtypeDeriving #-} -- deriving from 'newtype'

import Data.Monoid
import DList

{-
class Monoid a where
  mempty :: a
  mappend :: a -> a -> a
  mconcat :: [a] -> a
-}

{-
instance Monoid [a] where
  mempty = []
  mappend = (++)
-}

instance Monoid (DList a) where
  mempty = empty
  mappend = append

test1 = "foo" `mappend` "bar" -- "foobar"

test2 = toList (fromList [1,2] `mappend` fromList [3,4])  -- [1,2,3,4]

test3 = mempty `mappend` [1] -- [1]


newtype AInt = A { unA :: Int }
  deriving (Show, Eq, Num)

--monoid under addition
instance Monoid AInt where
  mempty = 0
  mappend = (+)

newtype MInt = M { unM :: Int }
  deriving (Show, Eq, Num)
--
-- monoid under multiplication
instance Monoid MInt where
  mempty = 1
  mappend = (*)

test4 = 2 `mappend` 5 :: MInt -- M {unM = 10}
test5 = 2 `mappend` 5 :: AInt -- A {UnA = 7}









