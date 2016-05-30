import Test.QuickCheck

{-
class Arbitrary a where
  arbitrary :: Gen a
-}

data Ternary = Yes | No | Unknown deriving Show

instance Arbitrary Ternary where
-- elements :: [a] -> Gen a
  arbitrary  = elements [Yes, No, Unknown]

data Ternary' = Yes' | No' | Unknown' deriving Show

instance Arbitrary Ternary' where
  arbitrary = do -- Gen is a monad
-- choose :: System.Random.Random a => (a, a) -> Gen a
    n <- choose (0,2) :: Gen Int
    return $ case n of
              0 -> Yes'
              1 -> No'
              2 -> Unknown'

{-
instance (Arbitrary a, Arbitrary b) => Arbitrary (a,b) where
  arbitrary = do
    x <- arbitrary
    y <- arbitrary
    return (x,y)
-}
