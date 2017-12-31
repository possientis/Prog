{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}


type family (a :: k) == (b :: k) :: Bool 
type instance a == b = EqStar a b
type instance a == b = EqArrow a b
type instance a == b = EqBool a b

type family EqStar (a :: *) (b :: *) where
    EqStar a a = True
    EqStar a b = False

type family EqArrow (a :: k1 -> k2) (b :: k1 -> k2) where
    EqArrow a a = True
    EqArrow a b = False

type family EqBool a b where
    EqBool True  True  = True
    EqBool False False = True
    EqBool a     b     = False


type family EqList a b where
    EqList '[]          '[]         = True
    EqList (a ': as)    (b ': bs)   = (a == b) && (as == bs) 
    EqList a b                      = False

type family a && b where
    True && True = True
    a    && b    = False
