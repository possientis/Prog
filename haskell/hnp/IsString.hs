{-# LANGUAGE OverloadedStrings #-}

import Data.String

data Foo = A | B | Other String deriving Show

instance IsString Foo where
    fromString "A" = A
    fromString "B" = B
    fromString xs  = Other xs

tests ::[Foo]
tests = ["A", "B", "Testing"]






