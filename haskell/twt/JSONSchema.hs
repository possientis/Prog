{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE UndecidableInstances   #-}

module JSONSchema where

import Data.Kind
import Data.Text
import Data.Aeson
import GHC.TypeLits
import GHC.Generics
import Data.Typeable
import Control.Monad.Writer
import Data.Aeson.Encode.Pretty
import qualified Data.Aeson.Types as T
import qualified Data.ByteString.Lazy.Char8 as LC8

data Person = Person
    { name    :: String
    , age     :: Int
    , phone   :: Maybe String
    , perms   :: [Bool]
    } deriving (Generic)     

class GSchema (a :: Type -> Type) where
    gschema :: Writer [Text] Value


mergeObjects :: Value -> Value -> Value
mergeObjects (Object a) (Object b) = Object $ a <> b
mergeObjects _ _ = error "illegal call"

emitRequired 
    :: forall nm
    .  KnownSymbol nm
    => Writer [Text] ()
emitRequired = tell . pure . pack . symbolVal $ Proxy @nm

type family ToJSONType (a :: Type) :: Symbol where
    ToJSONType Int      = "integer"
    ToJSONType Integer  = "integer"
    ToJSONType Float    = "number"
    ToJSONType Double   = "number"
    ToJSONType String   = "string"
    ToJSONType Bool     = "boolean"
    ToJSONType [a]      = "array"
    ToJSONType a        = TypeName a

type family RepName (x :: Type -> Type) :: Symbol where
    RepName (D1 ('MetaData nm _ _ _) _) = nm

type family TypeName (t :: Type) :: Symbol where
    TypeName t = RepName (Rep t)

makeTypeObj
    :: forall a
     . KnownSymbol (ToJSONType a)
    => Value
makeTypeObj = object 
    [ "type" .=
      String (pack . symbolVal $ Proxy @(ToJSONType a))
    ]

makePropertyObj
    :: forall name
     . (KnownSymbol name)
    => Value -> Value
makePropertyObj v = object
    [ pack (symbolVal $ Proxy @name) .= v
    ]

instance (KnownSymbol nm, KnownSymbol (ToJSONType a))
    => GSchema (M1 S ('MetaSel ('Just nm) _1 _2 _3)
                    (K1 _4 a)) where
    gschema = do
        emitRequired @ nm
        pure . makePropertyObj @nm
            $ makeTypeObj @a
    {-# INLINE gschema #-}

type T1 = ToJSONType Double
type T2 = ToJSONType String
type T3 = ToJSONType [Int]
type T4 = ToJSONType Person

t1 :: ((),[Text])
t1 = runWriter (emitRequired @"required property")

t2 :: Value
t2 = makeTypeObj @Int

