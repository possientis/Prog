{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE FlexibleContexts       #-}

import Data.Kind
import GHC.Generics

class GDef (a :: Type -> Type) where
    gdef :: Maybe (a x)

instance GDef U1 where
    gdef = Just U1

instance GDef V1 where
    gdef = Nothing

instance GDef (K1 _1 a) where
    gdef = Nothing

instance GDef (a :+: b) where
    gdef = Nothing

instance (GDef a, GDef b) => GDef (a :*: b) where
    gdef = do
        x <- gdef
        y <- gdef
        pure (x :*: y)

instance GDef (M1 _x _y a) where
    gdef = Nothing

exNihilo :: (Generic a, GDef (Rep a)) => Maybe a
exNihilo = to <$> gdef

data Test = Test deriving (Generic, Show)

-- does not work as expexted :( 
main :: IO ()
main =do
    print $ (exNihilo :: Maybe ())
    print $ (exNihilo :: Maybe Test)
