{-# LANGUAGE GeneralizedNewtypeDeriving     #-}

module  Error
    (   Error
    ,   mkError
    )   where


newtype Error = Error { _unError :: [String] }
    deriving (Semigroup, Monoid, Show)

mkError :: String -> Error
mkError s = Error [s]

