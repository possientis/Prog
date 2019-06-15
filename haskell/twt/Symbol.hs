{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}

import GHC.TypeLits

type S1 = ("Hello"  :: Symbol)
type S2 = (" World" :: Symbol)
type S3 = AppendSymbol S1 S2


