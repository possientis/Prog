import Test.HUnit

class (Eq a) =>  M a where 
  foo :: a -> String
  con :: Int -> a
  tests :: a -> Test
  tests x = let 
              y = (con 0)
              z = (x == y) 
            in
              TestCase (assertEqual "foo" (foo y)  "foo")


data A = A Int deriving Eq
data B = B Int deriving Eq

instance M A where
  foo _   = "foo"
  con     = A
  

instance M B where
  foo _   = "bar"     -- oops , implementation error
  con     = B


main = do
  runTestTT $ TestList 
    [ tests (A 0)
    , tests (B 0)
    ]
  
