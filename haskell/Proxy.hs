{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables       #-}


import Prelude      hiding (lookup)
import Data.Map

data Proxy a = Proxy

class Proxyable a where
    proxy :: Proxy a

instance Proxyable Int where
    proxy = Proxy


instance Proxyable Double where
    proxy = Proxy


instance Proxyable Char where
    proxy = Proxy

data ReadShowProxy = forall a . 
    (Read a, Show a, Proxyable a) => ReadShowProxy (Proxy a)


intProxy :: ReadShowProxy
intProxy = ReadShowProxy (Proxy :: Proxy Int)


dblProxy :: ReadShowProxy
dblProxy = ReadShowProxy (Proxy :: Proxy Double)


chrProxy :: ReadShowProxy
chrProxy = ReadShowProxy (Proxy :: Proxy Char)

-- Imagine "A", "B", "C" are column names of a relation
-- "A" ::: Int
-- "B" ::: Double
-- "C" ::: Char
-- The dictionary maps column names to a proxy of the type of the column

proxyDict :: Map String ReadShowProxy
proxyDict = fromList 
    [ ("A", intProxy)
    , ("B", dblProxy)
    , ("C", chrProxy)
    ]

-- This is an arbitrary function which requires a proxy input
someProxyFunction :: forall a. (Read a, Show a) => Proxy a -> String -> String
someProxyFunction _ s = show (read s :: a)


-- This is some client code attempting to use 'someProxyFunction'
-- for each column in the relation 
f :: String -> String -> Maybe String
f colName s = do
    ReadShowProxy p <- lookup colName proxyDict
    return $ someProxyFunction p s

main :: IO ()
main = do
    print $ f "A" "345"
    print $ f "B" "34.23"
    print $ f "C" "'T'"
    print $ f "A" "3.14"    -- Just "*** Exception: Prelude.read: no parse 

