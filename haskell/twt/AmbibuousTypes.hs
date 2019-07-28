{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

type family AlwaysUnit a where
    AlwaysUnit a = ()


type T1 a = AlwaysUnit a -> a
type T2 a b = b -> AlwaysUnit a -> b

-- cannot deduce a
f :: Show a => AlwaysUnit a -> String
f = undefined
