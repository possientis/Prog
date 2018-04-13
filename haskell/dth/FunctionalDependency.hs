{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

data Nat = Zero | Succ Nat

-- relation Pred on kind Nat is functional
class Pred (a :: Nat) (b :: Nat) | a -> b


instance Pred ('Succ n) n
instance Pred 'Zero 'Zero


class Plus (a :: Nat) (b :: Nat) (r :: Nat) | a b -> r

instance Plus 'Zero n n
instance Plus n m r => Plus ('Succ n) m ('Succ r)


