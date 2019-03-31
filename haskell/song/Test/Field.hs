module  Test.Field
    (   prop_add_comm
    ,   prop_mul_comm
    ,   prop_add_assoc
    ,   prop_mul_assoc
    ,   prop_add_inv_l
    ,   prop_add_inv_r
    ,   prop_mul_inv_l
    ,   prop_mul_inv_r
    ,   prop_add_id_l
    ,   prop_add_id_r
    ,   prop_mul_id_l
    ,   prop_mul_id_r
    ,   prop_sub
    ,   prop_div
    ,   prop_pow_zero
    ,   prop_pow_neg
    ,   prop_pow_mul
    )   where

import qualified Prelude    as P    ((+))
import           Prelude    hiding  ((+),(*),(-),(/))

import           Field

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

