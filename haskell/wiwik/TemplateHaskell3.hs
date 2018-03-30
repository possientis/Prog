{-# LANGUAGE TemplateHaskell #-}

import Language.Haskell.TH

foo :: Int -> Int
foo x = x + 1

data Bar


fooInfo :: InfoQ
fooInfo = reify 'foo


barInfo :: InfoQ
barInfo = reify ''Bar


$( [d| data T = T1 | T2 deriving Show |] )

main :: IO ()
main = print [T1,T2]


{-

ghc TemplateHaskell3.hs -ddump-splices

TemplateHaskell3.hs:19:4-40: Splicing declarations
    [d| data T_a3km
          = T1_a3kn | T2_a3ko
          deriving (Show) |]
  ======>
    data T_a4Oi
      = T1_a4Oj | T2_a4Ok
      deriving (Show)

-}
