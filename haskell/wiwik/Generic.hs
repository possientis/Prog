{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

class Generic a where
    type Rep a
    from :: a -> Rep a
    to :: Rep a -> a


class Datatype d where
    datatypeName :: t d f a -> String
    moduleName   :: t d f a -> String


class Constructor c where
    conMame :: t c f a -> String


infixr 5 :+:
data (:+:) f g p = L1 (f p) | R1 (g p)


infixr 6 :*:
data (:*:) f g p = f p :*: g p

-- tag for M1 datatype
data D

-- tag for M1 constructor
data C

-- constants, additional parameters and recursion of kind *
newtype K1 i c p = K1 { unK1 :: c }

-- meta-information (constructor names, etc )
newtype M1 i c f p = M1 { unM1 :: f p }

-- type synonym for encoding meta-information for datatypes
type D1 = M1 D

-- type synonym for encoding meta-information for constructors
type C1 = M1 C


