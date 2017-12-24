{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

import Prelude hiding (Bool(..))

data S a b = L a | R b

-- Default
-- S :: * -> * -> *     (type constructor)
-- L :: a -> S a b      (data constructor)
-- R :: b -> S a b      (data constructor) 


-- DataKinds
-- S :: * -> * -> *     (type constructor)
-- L :: a -> S a b      (data constructor)
-- L :: * -> S * *      (type constructor) (but :k fails in ghci)
-- R :: b -> S a b      (data constructor)
-- R :: * -> S * *      (type constructor) (but :k fails in ghci) 

-- promoted data constructor are not exported by default
-- This probably explains why :k fails in ghci for promoted data constuctor
-- However, type synonym can be created for export by module

type LL = 'L
type RR = 'R


data Bool = True | False

type family Not (a::Bool) :: Bool

type instance Not True  = False
type instance Not False = True

false :: Not True ~ False => a
false = undefined

true :: Not False ~ True => a
true = undefined

-- Fails at compile time.
-- Couldn't match type 'False with 'True

invalid :: Not True ~ True => a
invalid = undefined





