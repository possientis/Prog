{-# LANGUAGE TypeFamilies #-}

import Data.Set hiding (singleton)
import qualified Data.Set as Set (singleton)

-- a type family is simply a function on type

type family F1 a where
    F1 Int  = Bool
    F1 Char = Double


-- F1 is a closed type family : all of its defining equations are
-- given in one place

{- illegal instance for closed type family
type instance F1 Double = Int
-}

useF1 :: F1 Int-> F1 Char
useF1 True  = 1
useF1 False = -1


-- it is possible to define open type families : where the set of
-- defining equations can be extended arbitrarily. This works well
-- with type classes (which also allow arbirary extensions)

type family Element c

class Collection c where
    singleton :: Element c -> c

type instance Element [a] = a
instance Collection [a] where
    singleton x = [x]

type instance Element (Set a) = a
instance Collection (Set a) where
    singleton = Set.singleton

-- Because open type families are often asociated with a type class
-- GHC supports 'associated' open type families, using the following
-- syntax, which is just syntactic sugar for regular open type families

class Collection' c where
    type Element' c
    singleton' :: Element' c -> c

instance Collection' [a] where
    type Element' [a] = a
    singleton' x = [x]

instance Collection' (Set a) where
    type Element' (Set a) = a
    singleton' = Set.singleton

-- type aliasing
type List a = [a]

-- also type aliasing
type family List' a where
    List' a = [a]

test :: [a] -> a
test = head

xs :: List Int 
xs = [1]

ys :: List' Int
ys = [1]

-- both of these work
test1 = test xs
test2 = test ys







