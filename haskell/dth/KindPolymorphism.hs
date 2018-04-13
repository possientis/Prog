{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

-- Nat is a type, Zero and Succ are expression
-- But these can be promoted, so
-- Nat is also a kind, and 'Zero and 'Succ are type expressions
-- 'Zero has kind Nat, while 'Succ has kind Nat -> Nat.
data Nat = Zero | Succ Nat

-- defining a closed type family Length
-- using kind polymorpshim since using kind variable 'k' (it need not be 'k')
-- 'list' is a type variable here (it need not be 'list')
-- just as Zero and Succ, data constructors [] and (:) can be promoted
-- to type expression '[] and ': while [k] becomes a kind.
-- The kind annotation a :: [k] is optional 'Length a' works too.
type family Length (a :: [k]) :: Nat where
  Length '[]       = 'Zero
  Length (x ': xs) = 'Succ (Length xs)



