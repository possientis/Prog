-- see Roles.hs

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}


newtype Age = MkAge { unAge :: Int }

type family Inspect x
type instance Inspect Age = Int
type instance Inspect Int = Bool

class Boom a where
    boom :: a -> Inspect a

instance Boom Int where
    boom n = (n == 0)

deriving instance Boom Age --failure
