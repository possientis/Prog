{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE UndecidableInstances   #-}

module JSONSchema where

import Data.Kind
import Data.Text
import Data.Aeson
import GHC.TypeLits
import GHC.TypeLits
import Data.Typeable
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


