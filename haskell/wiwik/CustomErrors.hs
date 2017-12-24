{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

import GHC.TypeLits

instance 
    -- Error Message
    TypeError (Text "Equality is not defined for functions"
    :$$:
    (ShowType a :<>: Text "-> " :<>: ShowType b))


-- Instance head
    => Eq (a -> b) where (==) = undefined

-- Fail when we try to equate two functions
--ex = id == id

type family Coerce a b where
    Coerce Int Int      = Int
    Coerce Float Float  = Float
    Coerce Int Float    = Float
    Coerce Float Int    = TypeError (Text "Cannot cast to smaller type")


data Expr a where
    EInt    :: Int -> Expr Int
    EFloat  :: Float -> Expr Float
    ECoerce :: Expr b -> Expr c -> Expr (Coerce b c)

-- Cannot cast to a smaller type
foo :: Expr Int
foo =  ECoerce (EFloat 3) (EInt 3)
