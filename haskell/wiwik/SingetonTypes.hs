{-# LANGUAGE KindSignatures #-}

import GHC.Types


type family Sing (a :: Nat)

data instance Sing (a :: Nat) where
    SZ :: Sing 'Z
    SS :: Sing n -> Sing ('S n)


-- TODO



