{-# LANGUAGE OverloadedStrings #-}

import Data.String.Conversions

import qualified Data.Text as T
import qualified Data.Text.Lazy.IO as TL
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Lazy.Char8 as BL

import Data.Monoid

a :: String
a = "Godel"

b :: BL.ByteString
b = "Einstein"

c :: T.Text
c = "Feynmann"

d :: B.ByteString
d = "Schrodinger"


-- Compare unlike strings 
(==~) :: (Eq a, ConvertibleStrings b a) => a -> b -> Bool
(==~) a b = a == convertString b

-- Concat unlike strings
(<>~) :: (Monoid a, ConvertibleStrings b a) => a -> b -> a
(<>~) a b = a <> convertString b


main :: IO ()
main = do
    putStrLn (convertString a)
    putStrLn (convertString b)
    putStrLn (convertString c)
    putStrLn (convertString d)
    TL.putStrLn (convertString a)
    TL.putStrLn (convertString b)
    TL.putStrLn (convertString c)
    TL.putStrLn (convertString d)
    B.putStrLn (convertString a)
    B.putStrLn (convertString b)
    B.putStrLn (convertString c)
    B.putStrLn (convertString d)
    BL.putStrLn (convertString a)
    BL.putStrLn (convertString b)
    BL.putStrLn (convertString c)
    BL.putStrLn (convertString d)
    print (a ==~ a)
    print (a ==~ b)
    print (a ==~ c)
    print (a ==~ d)
    print (b ==~ a)
    print (b ==~ b)
    print (b ==~ c)
    print (b ==~ d)







