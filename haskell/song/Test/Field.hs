{-# LANGUAGE ScopedTypeVariables #-}

module  Test.Field
    (   fieldTests
    ,   testPrime
    )   where

import qualified Prelude        as P    ((+))
import           Prelude        hiding  ((+),(*),(-),(/))
import           Data.Proxy
import           Test.Hspec
import           Test.QuickCheck

import           Field
import           HasPrime

testPrime :: forall a . (HasPrime a) => Proxy a -> Integer -> Spec
testPrime _ p = it ("checked underlying prime is correct") $ 
    prime (Proxy :: Proxy a) `shouldBe` p

fieldTests :: forall a. (Field a, Show a, Arbitrary a) => [Proxy a -> Spec]
fieldTests =
    [   test_add_comm
    ,   test_mul_comm
    ,   test_add_assoc
    ,   test_mul_assoc
    ,   test_add_inv_l
    ,   test_add_inv_r
    ,   test_mul_inv_l
    ,   test_mul_inv_r
    ,   test_add_id_l
    ,   test_add_id_r
    ,   test_mul_id_l
    ,   test_mul_id_r
    ,   test_sub
    ,   test_div
    ,   test_pow_zero
    ,   test_pow_neg
    ,   test_pow_mul
    ] 
test_add_comm :: forall a .(Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_add_comm _ = it "Checked addition is commutative" $ 
    property $ (prop_add_comm :: a -> a -> Bool)

test_mul_comm :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_mul_comm _ = it "Checked multiplication is commutative" $ 
    property $ (prop_mul_comm :: a -> a -> Bool)

test_add_assoc :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_add_assoc _ = it "Checked addition is associative" $ 
    property $ (prop_add_assoc :: a -> a -> a -> Bool)

test_mul_assoc :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_mul_assoc _ = it "Checked multiplication is associative" $ 
    property $ (prop_mul_assoc :: a -> a -> a -> Bool)

test_add_inv_l :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_add_inv_l _ = it "Checked left-inverse law for addition" $ 
    property $ (prop_add_inv_l :: a -> Bool)

test_add_inv_r :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_add_inv_r _ = it "Checked right-inverse law for addition" $ 
    property $ (prop_add_inv_r :: a -> Bool)

test_mul_inv_l :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_mul_inv_l _ = it "Checked left-inverse law for multiplication" $ 
    property $ (prop_mul_inv_l :: a -> Bool)

test_mul_inv_r :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_mul_inv_r _ = it "Checked right-inverse law for multiplication" $ 
    property $ (prop_mul_inv_r :: a -> Bool)

test_add_id_l :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_add_id_l _ = it "Checked left-identity law for addition" $ 
    property $ (prop_add_id_l :: a -> Bool)

test_add_id_r :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_add_id_r _ = it "Checked right-identity law for addition" $ 
    property $ (prop_add_id_r :: a -> Bool)

test_mul_id_l :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_mul_id_l _ = it "Checked left-identity law for multiplication" $ 
    property $ (prop_mul_id_l :: a -> Bool)

test_mul_id_r :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_mul_id_r _ = it "Checked right-identity law for multiplication" $ 
    property $ (prop_mul_id_r :: a -> Bool)

test_sub :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_sub _ = it "Checked subtraction" $ 
    property $ (prop_sub :: a -> a -> Bool)

test_div :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_div _ = it "Checked division" $ 
    property $ (prop_div :: a -> a -> Bool)

test_pow_zero :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_pow_zero _ = it "Checked for zero power" $ 
    property $ (prop_pow_zero :: a -> Bool)

test_pow_neg :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_pow_neg _ = it "Checked for negative power" $ 
    property $ (prop_pow_neg :: a -> Integer -> Bool)

test_pow_mul :: forall a . (Field a, Show a, Arbitrary a) => Proxy a -> Spec
test_pow_mul _ = it "Checked for multiplying power" $ 
    property $ (prop_pow_mul :: a -> Integer -> Integer -> Bool)

prop_add_comm :: (Field a) => a -> a -> Bool
prop_add_comm x y = x + y == y + x
 
prop_mul_comm :: (Field a) => a -> a -> Bool
prop_mul_comm x y = x * y == y * x

prop_add_assoc :: (Field a) => a -> a -> a -> Bool
prop_add_assoc x y z = (x + y) + z == x + (y + z)

prop_mul_assoc :: (Field a) => a -> a -> a -> Bool
prop_mul_assoc x y z = (x * y) * z == x * (y * z)

prop_add_inv_l :: (Field a) => a -> Bool
prop_add_inv_l x = (neg x) + x == zero 

prop_add_inv_r :: (Field a) => a -> Bool
prop_add_inv_r x = x + (neg x) == zero 

prop_mul_inv_l :: (Field a) => a -> Bool
prop_mul_inv_l x = if x /= zero 
    then (inv x) * x == one
    else True 

prop_mul_inv_r :: (Field a) => a -> Bool
prop_mul_inv_r x = if x /= zero 
    then x * (inv x) == one
    else True 

prop_add_id_l :: (Field a) => a -> Bool
prop_add_id_l x = zero + x == x

prop_add_id_r :: (Field a) => a -> Bool
prop_add_id_r x = x + zero == x

prop_mul_id_l :: (Field a) => a -> Bool
prop_mul_id_l x = one * x == x

prop_mul_id_r :: (Field a) => a -> Bool
prop_mul_id_r x = x * one == x

prop_sub :: (Field a) => a -> a -> Bool
prop_sub x y = x - y == x + (neg y)

prop_div :: (Field a) => a -> a -> Bool
prop_div x y = if y /= zero
    then x / y == x * (inv y)
    else True

prop_pow_zero :: (Field a) => a -> Bool
prop_pow_zero  x = pow x 0 == one

prop_pow_neg :: (Field a) => a -> Integer -> Bool
prop_pow_neg  x k  = if x /= zero 
    then pow x (-k) == pow (inv x) k
    else True 
 
prop_pow_mul :: (Field a) => a -> Integer -> Integer -> Bool
prop_pow_mul x n m = if ((x /= zero) || (n >= 0 && m >= 0))
    then pow x (n P.+ m) == pow x n * pow x m  
    else True

