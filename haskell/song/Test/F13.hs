module  Test.F13
    (   specF13
    )   where

import           Prelude    hiding  ((+),(*),(-),(/))
import           Test.Hspec
import           Test.QuickCheck

import           F13
import           Test.Field

specF13 :: Spec
specF13 = describe "Checking Field F13..." $ 
    sequence_ specsF13

specsF13 :: [Spec]
specsF13 =  [ test_add_comm_F13
            , test_mul_comm_F13
            , test_add_assoc_F13
            , test_mul_assoc_F13
            , test_add_inv_l_F13
            , test_add_inv_r_F13
            , test_mul_inv_l_F13
            , test_mul_inv_r_F13
            , test_add_id_l_F13
            , test_add_id_r_F13
            , test_mul_id_l_F13
            , test_mul_id_r_F13
            , test_sub_F13
            , test_div_F13
            , test_pow_zero_F13
            , test_pow_neg_F13
            , test_pow_mul_F13
            ]

test_add_comm_F13 :: Spec
test_add_comm_F13 = it "Checked F13 addition is commutative" $ 
    property $ (prop_add_comm :: F13 -> F13 -> Bool)

test_mul_comm_F13 :: Spec
test_mul_comm_F13 = it "Checked F13 multiplication is commutative" $ 
    property $ (prop_mul_comm :: F13 -> F13 -> Bool)

test_add_assoc_F13 :: Spec
test_add_assoc_F13 = it "Checked F13 addition is associative" $ 
    property $ (prop_add_assoc :: F13 -> F13 -> F13 -> Bool)

test_mul_assoc_F13 :: Spec
test_mul_assoc_F13 = it "Checked F13 multiplication is associative" $ 
    property $ (prop_mul_assoc :: F13 -> F13 -> F13 -> Bool)

test_add_inv_l_F13 :: Spec
test_add_inv_l_F13 = it "Checked F13 left-inverse law for addition" $ 
    property $ (prop_add_inv_l :: F13 -> Bool)

test_add_inv_r_F13 :: Spec
test_add_inv_r_F13 = it "Checked F13 right-inverse law for addition" $ 
    property $ (prop_add_inv_r :: F13 -> Bool)

test_mul_inv_l_F13 :: Spec
test_mul_inv_l_F13 = it "Checked F13 left-inverse law for multiplication" $ 
    property $ (prop_mul_inv_l :: F13 -> Bool)

test_mul_inv_r_F13 :: Spec
test_mul_inv_r_F13 = it "Checked F13 right-inverse law for multiplication" $ 
    property $ (prop_mul_inv_r :: F13 -> Bool)

test_add_id_l_F13 :: Spec
test_add_id_l_F13 = it "Checked F13 left-identity law for addition" $ 
    property $ (prop_add_id_l :: F13 -> Bool)

test_add_id_r_F13 :: Spec
test_add_id_r_F13 = it "Checked F13 right-identity law for addition" $ 
    property $ (prop_add_id_r :: F13 -> Bool)

test_mul_id_l_F13 :: Spec
test_mul_id_l_F13 = it "Checked F13 left-identity law for multiplication" $ 
    property $ (prop_mul_id_l :: F13 -> Bool)

test_mul_id_r_F13 :: Spec
test_mul_id_r_F13 = it "Checked F13 right-identity law for multiplication" $ 
    property $ (prop_mul_id_r :: F13 -> Bool)

test_sub_F13 :: Spec
test_sub_F13 = it "Checked F13 subtraction" $ 
    property $ (prop_sub :: F13 -> F13 -> Bool)

test_div_F13 :: Spec
test_div_F13 = it "Checked F13 division" $ 
    property $ (prop_div :: F13 -> F13 -> Bool)

test_pow_zero_F13 :: Spec
test_pow_zero_F13 = it "Checked F13 for zero power" $ 
    property $ (prop_pow_zero :: F13 -> Bool)

test_pow_neg_F13 :: Spec
test_pow_neg_F13 = it "Checked F13 for negative power" $ 
    property $ (prop_pow_neg :: F13 -> Integer -> Bool)

test_pow_mul_F13 :: Spec
test_pow_mul_F13 = it "Checked F13 for multiplying power" $ 
    property $ (prop_pow_mul :: F13 -> Integer -> Integer -> Bool)

