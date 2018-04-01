{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}

import GHC.TypeLits
import Data.Proxy

import EnumFamily


type family Mod (n :: Nat) (m :: Nat) :: Nat
type family Add (n :: Nat) (m :: Nat) :: Nat
type family Pow (n :: Nat) (m :: Nat) :: Nat


enumFamily mod ''Mod 10
enumFamily (+) ''Add 10
enumFamily (^) ''Pow 10

a :: Integer
a = natVal (Proxy :: Proxy (Mod 6 4))
-- 2


b ::Integer 
b = natVal (Proxy :: Proxy (Pow 3 (Mod 6 4)))
-- 9

{- ghc -ddump-splices EnumFamily2.hs
 -
EnumFamily2.hs:16:1-23: Splicing declarations
    enumFamily mod ''Mod 10
  ======>
    type instance Mod 1 2 = 1
    type instance Mod 1 3 = 1
    type instance Mod 1 4 = 1
    type instance Mod 1 5 = 1
    type instance Mod 1 6 = 1
    type instance Mod 1 7 = 1
    type instance Mod 1 8 = 1
    type instance Mod 1 9 = 1
    type instance Mod 1 10 = 1
    type instance Mod 2 2 = 0
    type instance Mod 2 3 = 2
    type instance Mod 2 4 = 2
    type instance Mod 2 5 = 2
    type instance Mod 2 6 = 2
    type instance Mod 2 7 = 2
    type instance Mod 2 8 = 2
    type instance Mod 2 9 = 2
    type instance Mod 2 10 = 2
    type instance Mod 3 2 = 1
    type instance Mod 3 3 = 0
    type instance Mod 3 4 = 3
    type instance Mod 3 5 = 3
    type instance Mod 3 6 = 3
    type instance Mod 3 7 = 3
    type instance Mod 3 8 = 3
    type instance Mod 3 9 = 3
    type instance Mod 3 10 = 3
    type instance Mod 4 2 = 0
    type instance Mod 4 3 = 1
    type instance Mod 4 4 = 0
    type instance Mod 4 5 = 4
    type instance Mod 4 6 = 4
    type instance Mod 4 7 = 4
    type instance Mod 4 8 = 4
    type instance Mod 4 9 = 4
    type instance Mod 4 10 = 4
    type instance Mod 5 2 = 1
    type instance Mod 5 3 = 2
    type instance Mod 5 4 = 1
    type instance Mod 5 5 = 0
    type instance Mod 5 6 = 5
    type instance Mod 5 7 = 5
    type instance Mod 5 8 = 5
    type instance Mod 5 9 = 5
    type instance Mod 5 10 = 5
    type instance Mod 6 2 = 0
    type instance Mod 6 3 = 0
    type instance Mod 6 4 = 2
    type instance Mod 6 5 = 1
    type instance Mod 6 6 = 0
    type instance Mod 6 7 = 6
    type instance Mod 6 8 = 6
    type instance Mod 6 9 = 6
    type instance Mod 6 10 = 6
    type instance Mod 7 2 = 1
    type instance Mod 7 3 = 1
    type instance Mod 7 4 = 3
    type instance Mod 7 5 = 2
    type instance Mod 7 6 = 1
    type instance Mod 7 7 = 0
    type instance Mod 7 8 = 7
    type instance Mod 7 9 = 7
    type instance Mod 7 10 = 7
    type instance Mod 8 2 = 0
    type instance Mod 8 3 = 2
    type instance Mod 8 4 = 0
    type instance Mod 8 5 = 3
    type instance Mod 8 6 = 2
    type instance Mod 8 7 = 1
    type instance Mod 8 8 = 0
    type instance Mod 8 9 = 8
    type instance Mod 8 10 = 8
    type instance Mod 9 2 = 1
    type instance Mod 9 3 = 0
    type instance Mod 9 4 = 1
    type instance Mod 9 5 = 4
    type instance Mod 9 6 = 3
    type instance Mod 9 7 = 2
    type instance Mod 9 8 = 1
    type instance Mod 9 9 = 0
    type instance Mod 9 10 = 9
    type instance Mod 10 2 = 0
    type instance Mod 10 3 = 1
    type instance Mod 10 4 = 2
    type instance Mod 10 5 = 0
    type instance Mod 10 6 = 4
    type instance Mod 10 7 = 3
    type instance Mod 10 8 = 2
    type instance Mod 10 9 = 1
    type instance Mod 10 10 = 0
EnumFamily2.hs:17:1-23: Splicing declarations
    enumFamily (+) ''Add 10
  ======>
    type instance Add 1 2 = 3
    type instance Add 1 3 = 4
    type instance Add 1 4 = 5
    type instance Add 1 5 = 6
    type instance Add 1 6 = 7
    type instance Add 1 7 = 8
    type instance Add 1 8 = 9
    type instance Add 1 9 = 10
    type instance Add 1 10 = 11
    type instance Add 2 2 = 4
    type instance Add 2 3 = 5
    type instance Add 2 4 = 6
    type instance Add 2 5 = 7
    type instance Add 2 6 = 8
    type instance Add 2 7 = 9
    type instance Add 2 8 = 10
    type instance Add 2 9 = 11
    type instance Add 2 10 = 12
    type instance Add 3 2 = 5
    type instance Add 3 3 = 6
    type instance Add 3 4 = 7
    type instance Add 3 5 = 8
    type instance Add 3 6 = 9
    type instance Add 3 7 = 10
    type instance Add 3 8 = 11
    type instance Add 3 9 = 12
    type instance Add 3 10 = 13
    type instance Add 4 2 = 6
    type instance Add 4 3 = 7
    type instance Add 4 4 = 8
    type instance Add 4 5 = 9
    type instance Add 4 6 = 10
    type instance Add 4 7 = 11
    type instance Add 4 8 = 12
    type instance Add 4 9 = 13
    type instance Add 4 10 = 14
    type instance Add 5 2 = 7
    type instance Add 5 3 = 8
    type instance Add 5 4 = 9
    type instance Add 5 5 = 10
    type instance Add 5 6 = 11
    type instance Add 5 7 = 12
    type instance Add 5 8 = 13
    type instance Add 5 9 = 14
    type instance Add 5 10 = 15
    type instance Add 6 2 = 8
    type instance Add 6 3 = 9
    type instance Add 6 4 = 10
    type instance Add 6 5 = 11
    type instance Add 6 6 = 12
    type instance Add 6 7 = 13
    type instance Add 6 8 = 14
    type instance Add 6 9 = 15
    type instance Add 6 10 = 16
    type instance Add 7 2 = 9
    type instance Add 7 3 = 10
    type instance Add 7 4 = 11
    type instance Add 7 5 = 12
    type instance Add 7 6 = 13
    type instance Add 7 7 = 14
    type instance Add 7 8 = 15
    type instance Add 7 9 = 16
    type instance Add 7 10 = 17
    type instance Add 8 2 = 10
    type instance Add 8 3 = 11
    type instance Add 8 4 = 12
    type instance Add 8 5 = 13
    type instance Add 8 6 = 14
    type instance Add 8 7 = 15
    type instance Add 8 8 = 16
    type instance Add 8 9 = 17
    type instance Add 8 10 = 18
    type instance Add 9 2 = 11
    type instance Add 9 3 = 12
    type instance Add 9 4 = 13
    type instance Add 9 5 = 14
    type instance Add 9 6 = 15
    type instance Add 9 7 = 16
    type instance Add 9 8 = 17
    type instance Add 9 9 = 18
    type instance Add 9 10 = 19
    type instance Add 10 2 = 12
    type instance Add 10 3 = 13
    type instance Add 10 4 = 14
    type instance Add 10 5 = 15
    type instance Add 10 6 = 16
    type instance Add 10 7 = 17
    type instance Add 10 8 = 18
    type instance Add 10 9 = 19
    type instance Add 10 10 = 20
EnumFamily2.hs:18:1-23: Splicing declarations
    enumFamily (^) ''Pow 10
  ======>
    type instance Pow 1 2 = 1
    type instance Pow 1 3 = 1
    type instance Pow 1 4 = 1
    type instance Pow 1 5 = 1
    type instance Pow 1 6 = 1
    type instance Pow 1 7 = 1
    type instance Pow 1 8 = 1
    type instance Pow 1 9 = 1
    type instance Pow 1 10 = 1
    type instance Pow 2 2 = 4
    type instance Pow 2 3 = 8
    type instance Pow 2 4 = 16
    type instance Pow 2 5 = 32
    type instance Pow 2 6 = 64
    type instance Pow 2 7 = 128
    type instance Pow 2 8 = 256
    type instance Pow 2 9 = 512
    type instance Pow 2 10 = 1024
    type instance Pow 3 2 = 9
    type instance Pow 3 3 = 27
    type instance Pow 3 4 = 81
    type instance Pow 3 5 = 243
    type instance Pow 3 6 = 729
    type instance Pow 3 7 = 2187
    type instance Pow 3 8 = 6561
    type instance Pow 3 9 = 19683
    type instance Pow 3 10 = 59049
    type instance Pow 4 2 = 16
    type instance Pow 4 3 = 64
    type instance Pow 4 4 = 256
    type instance Pow 4 5 = 1024
    type instance Pow 4 6 = 4096
    type instance Pow 4 7 = 16384
    type instance Pow 4 8 = 65536
    type instance Pow 4 9 = 262144
    type instance Pow 4 10 = 1048576
    type instance Pow 5 2 = 25
    type instance Pow 5 3 = 125
    type instance Pow 5 4 = 625
    type instance Pow 5 5 = 3125
    type instance Pow 5 6 = 15625
    type instance Pow 5 7 = 78125
    type instance Pow 5 8 = 390625
    type instance Pow 5 9 = 1953125
    type instance Pow 5 10 = 9765625
    type instance Pow 6 2 = 36
    type instance Pow 6 3 = 216
    type instance Pow 6 4 = 1296
    type instance Pow 6 5 = 7776
    type instance Pow 6 6 = 46656
    type instance Pow 6 7 = 279936
    type instance Pow 6 8 = 1679616
    type instance Pow 6 9 = 10077696
    type instance Pow 6 10 = 60466176
    type instance Pow 7 2 = 49
    type instance Pow 7 3 = 343
    type instance Pow 7 4 = 2401
    type instance Pow 7 5 = 16807
    type instance Pow 7 6 = 117649
    type instance Pow 7 7 = 823543
    type instance Pow 7 8 = 5764801
    type instance Pow 7 9 = 40353607
    type instance Pow 7 10 = 282475249
    type instance Pow 8 2 = 64
    type instance Pow 8 3 = 512
    type instance Pow 8 4 = 4096
    type instance Pow 8 5 = 32768
    type instance Pow 8 6 = 262144
    type instance Pow 8 7 = 2097152
    type instance Pow 8 8 = 16777216
    type instance Pow 8 9 = 134217728
    type instance Pow 8 10 = 1073741824
    type instance Pow 9 2 = 81
    type instance Pow 9 3 = 729
    type instance Pow 9 4 = 6561
    type instance Pow 9 5 = 59049
    type instance Pow 9 6 = 531441
    type instance Pow 9 7 = 4782969
    type instance Pow 9 8 = 43046721
    type instance Pow 9 9 = 387420489
    type instance Pow 9 10 = 3486784401
    type instance Pow 10 2 = 100
    type instance Pow 10 3 = 1000
    type instance Pow 10 4 = 10000
    type instance Pow 10 5 = 100000
    type instance Pow 10 6 = 1000000
    type instance Pow 10 7 = 10000000
    type instance Pow 10 8 = 100000000
    type instance Pow 10 9 = 1000000000
    type instance Pow 10 10 = 10000000000
-}
