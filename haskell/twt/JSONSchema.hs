{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}

import Data.Kind
import Data.Text
import Data.Aeson
import GHC.TypeLits
import Control.Monad.Writer

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


