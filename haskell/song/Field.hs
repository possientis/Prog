{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module  Field
    (   F2   
    )   where

import Nat
import Prelude hiding (toInteger, fromInteger)

type family Field a where
    Field 'Z     = Integer
    Field ('I a) = Integer
    Field ('O a) = Integer

type Two = 'I ('O 'Z)

type F2 = Field Two


