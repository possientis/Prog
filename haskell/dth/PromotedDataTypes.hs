{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

data Nat = Zero | Succ Nat

-- kind inference is taking place here
--type family a + b where

-- possible to fully annotate kinds
type family (a::Nat) + (b::Nat) :: Nat where
  -- Data constructor Zero is not a type. However,
  -- we can promote it as a type, using DataKinds
  -- Now 'Zero becomes a type, and Nat becomes a kind
  -- and 'Zero has kind Nat.
  'Zero + b   = b
  -- 'Succ is now a type with kind Nat -> Nat 
  'Succ a + b = 'Succ (a + b) 



-- E1 has kind Nat, which is not *
type E1 = 'Succ 'Zero + 'Succ ('Succ 'Zero)


