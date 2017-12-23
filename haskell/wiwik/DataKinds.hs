{-# LANGUAGE DataKinds #-}

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

