module Main
  ( main
  ) where

import AffineWitness
import Affine
import Choice
import Iso
import IsoWitness
import Lens
import LensWitness
import Optic
import Prism
import PrismWitness
import Profunctor
import Strong

type A = (Int, Either String B, B)

type B = (Int, Either String Int)

b1:: B
b1 =  (1,Left "bbb")

b2 :: B
b2 = (2,Right 2)

a1 :: A
a1 = (1,Left "aaa",b2)

a2 :: A
a2 = (2,Right b1,b2)

a3 :: A
a3 = (3,Right b2,b2)

main :: IO ()
main = do
  undefined
