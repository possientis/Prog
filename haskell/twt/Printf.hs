{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE ScopedTypeVariables    #-}


import Data.Kind
import Data.Proxy
import GHC.TypeLits

data (a :: k1) :<< (b :: k2)
infixr 5 :<<

type T1 = Int :<< ":" :<< Bool :<< "!"

class HasPrintf a where
    type Printf a :: Type
    format :: String -> Proxy a -> Printf a


instance KnownSymbol text => HasPrintf (text :: Symbol) where
    type Printf text = String
    format s _ = s ++ symbolVal (Proxy @text)

instance (HasPrintf a, KnownSymbol text) => 
    HasPrintf ((text :: Symbol) :<< a) where
    type Printf (text :<< a) = Printf a
    format s _ = format (s ++ symbolVal (Proxy @text)) (Proxy @a)

instance (HasPrintf a, Show param) => 
    HasPrintf ((param :: Type) :<< a) where
    type Printf (param :<< a) = param -> Printf a
    format s _ param = format (s ++ show param) (Proxy @a)

instance {-# OVERLAPPING #-} HasPrintf a =>
    HasPrintf (String :<< a) where
    type Printf (String :<< a) = String -> Printf a
    format s _ param = format (s ++ param) (Proxy @a)

-- kind! T2 = Int -> Bool -> String
type T2 = Printf T1


printf :: HasPrintf a => Proxy a -> Printf a
printf = format ""

main :: IO ()
main = do
    print $ printf (Proxy @ "test")
    print $ printf (Proxy @(Int :<< " + " :<< Int :<< "= 3")) 1 2
    print $ printf (Proxy @(String :<< " world!")) "hello"
