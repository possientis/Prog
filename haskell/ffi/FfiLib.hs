module FfiLib
    ( double
    , triple
    ) where

foreign import ccall "fdouble" double :: Double -> Double
foreign import ccall "triple"  triple :: Double -> Double
