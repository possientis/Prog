module  Error
    (   Error   (..)
    )   where

newtype Error = Error { unError :: [String] }
