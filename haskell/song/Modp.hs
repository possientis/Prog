{-# LANGUAGE DataKinds  #-}

module  Modp
    (   Modp
    )   where

import Modular

type Modp = Mod 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
