{-# LANGUAGE ScopedTypeVariables, RankNTypes #-} -- used for scoped type variables
{-# LANGUAGE AllowAmbiguousTypes, TypeApplications #-}

import Test.HUnit
import Data.Proxy hiding (Proxy(..), asProxyTypeOf) -- we re doing it ourselves here

class M a where 
  foo :: a -> String
  cons :: Int -> a

data A = A Int
data B = B Int

instance M A where
  foo _   = "foo"
  cons    = A

instance M B where
  foo _   = "bar"     -- implementation error
  cons    = B

-- Proxy
data Proxy a = Proxy  -- nullary constructor, but parameterized type

asProxyTypeOf :: a -> Proxy a -> a
asProxyTypeOf = const -- asProxyTypeOf x proxy = x

test1 :: M a => Proxy a -> Test
test1 x = TestCase (assertEqual "foo" (foo (cons 0 `asProxyTypeOf` x)) "foo")

tests1 = TestList 
  [ test1 (Proxy :: Proxy A)
  , test1 (Proxy :: Proxy B)
  ]

-- proxy : type variable of kind * -> *
test2 :: M a => proxy a -> Test
test2 x = TestCase (assertEqual "foo" (foo (cons 0 `asProxyTypeOf` x)) "foo") 
  where 
    asProxyTypeOf :: a -> proxy a -> a
    asProxyTypeOf = const

tests2 = TestList 
  [ test2 ([] :: [A])         -- [] :: * -> *
  , test2 (Proxy :: Proxy B)  -- Proxy :: * -> * 
  ]

-- no more need for 'asProxyTypeOf'
-- Scoped type variables ('a' bound by top level signature)
test3 :: forall a proxy. M a => proxy a -> Test
test3 _ = TestCase (assertEqual "foo" (foo (cons 0 :: a)) "foo")

tests3 = TestList 
  [ test3 (Proxy :: Proxy A)  
  , test3 ([] :: [B])
  ]

-- from GHC v8 onwards, no need for the Proxy argument
-- 'a' bound by top level signature
test4 :: forall a. M a => Test
test4 = TestCase (assertEqual "foo" (foo (cons 0 :: a)) "foo")

tests4 = TestList 
  [ test4 @A
  , test4 @B
  ]



tests = TestList [tests1, tests2, tests3, tests4]

main = do
  runTestTT tests
  
