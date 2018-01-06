{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE UndecidableInstances #-}

import GHC.TypeLits
import Data.Type.Equality

type Z = 0


type family S (n :: Nat) :: Nat where
    S n = n + 1

-- Yes !
eq_zero :: Z :~: Z
eq_zero = Refl


-- Yes !
zero_plus_one :: (Z + 1) :~: (1 + Z)
zero_plus_one = Refl


-- Yes !
plus_zero :: forall n. (n + Z) :~: n
plus_zero = Refl


-- Yes !
plus_one :: forall n. (n + S Z) :~: S n
plus_one = Refl

{-
-- No
plus_n_Sm :: forall n m. (n + (S m)) :~: S (n + m)
plus_n_Sm = Refl
-}


