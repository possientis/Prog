module  Test.R
    (   specR
    )   where

import           Prelude    hiding  ((+),(*),(-),(/))
import           Test.Hspec
import           Test.QuickCheck

import           R
import           Test.Field

specR :: Spec
specR = describe "Checking Field R..." $ 
    sequence_ specsR

specsR :: [Spec]
specsR =  [ test_add_comm_R
          , test_mul_comm_R
          , test_add_assoc_R
          , test_mul_assoc_R
          , test_add_inv_l_R
          , test_add_inv_r_R
          , test_mul_inv_l_R
          , test_mul_inv_r_R
          , test_add_id_l_R
          , test_add_id_r_R
          , test_mul_id_l_R
          , test_mul_id_r_R
          , test_sub_R
          , test_div_R
          , test_pow_zero_R
          , test_pow_neg_R
          , test_pow_mul_R
          ]

test_add_comm_R :: Spec
test_add_comm_R = it "Checked R addition is commutative" $ 
    property $ (prop_add_comm :: R -> R -> Bool)

test_mul_comm_R :: Spec
test_mul_comm_R = it "Checked R multiplication is commutative" $ 
    property $ (prop_mul_comm :: R -> R -> Bool)

test_add_assoc_R :: Spec
test_add_assoc_R = it "Checked R addition is associative" $ 
    property $ (prop_add_assoc :: R -> R -> R -> Bool)

test_mul_assoc_R :: Spec
test_mul_assoc_R = it "Checked R multiplication is associative" $ 
    property $ (prop_mul_assoc :: R -> R -> R -> Bool)

test_add_inv_l_R :: Spec
test_add_inv_l_R = it "Checked R left-inverse law for addition" $ 
    property $ (prop_add_inv_l :: R -> Bool)

test_add_inv_r_R :: Spec
test_add_inv_r_R = it "Checked R right-inverse law for addition" $ 
    property $ (prop_add_inv_r :: R -> Bool)

test_mul_inv_l_R :: Spec
test_mul_inv_l_R = it "Checked R left-inverse law for multiplication" $ 
    property $ (prop_mul_inv_l :: R -> Bool)

test_mul_inv_r_R :: Spec
test_mul_inv_r_R = it "Checked R right-inverse law for multiplication" $ 
    property $ (prop_mul_inv_r :: R -> Bool)

test_add_id_l_R :: Spec
test_add_id_l_R = it "Checked R left-identity law for addition" $ 
    property $ (prop_add_id_l :: R -> Bool)

test_add_id_r_R :: Spec
test_add_id_r_R = it "Checked R right-identity law for addition" $ 
    property $ (prop_add_id_r :: R -> Bool)

test_mul_id_l_R :: Spec
test_mul_id_l_R = it "Checked R left-identity law for multiplication" $ 
    property $ (prop_mul_id_l :: R -> Bool)

test_mul_id_r_R :: Spec
test_mul_id_r_R = it "Checked R right-identity law for multiplication" $ 
    property $ (prop_mul_id_r :: R -> Bool)

test_sub_R :: Spec
test_sub_R = it "Checked R subtraction" $ 
    property $ (prop_sub :: R -> R -> Bool)

test_div_R :: Spec
test_div_R = it "Checked R division" $ 
    property $ (prop_div :: R -> R -> Bool)

test_pow_zero_R :: Spec
test_pow_zero_R = it "Checked R for zero power" $ 
    property $ (prop_pow_zero :: R -> Bool)

test_pow_neg_R :: Spec
test_pow_neg_R = it "Checked R for negative power" $ 
    property $ (prop_pow_neg :: R -> Integer -> Bool)

test_pow_mul_R :: Spec
test_pow_mul_R = it "Checked R for multiplying power" $ 
    property $ (prop_pow_mul :: R -> Integer -> Integer -> Bool)

