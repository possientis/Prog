module  Number.F2m
    (   BinaryPolynomial
    ,   addF2m
    )   where

import Data.Bits (xor)
import Number.Basic

-- | Binary Polynomial (i.e. element of Z2[X]) represented by an integer.
type BinaryPolynomial = Integer

-- | Addition over F₂m. This is just a synonym of 'xor'.
addF2m :: Integer
       -> Integer
       -> Integer
addF2m = xor

