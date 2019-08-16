{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeSynonymInstances   #-}

import Data.Kind
import Data.Typeable

data Has (c :: Type -> Constraint) where
    Has :: c t => t -> Has c 

type HasShow     = Has Show
type Dynamic     = Has Typeable

elimHas 
    :: (forall a . c a => a -> r) 
    -> Has c
    -> r
elimHas f (Has x) = f x

instance Show HasShow where
    show = elimHas show

isMempty :: (Monoid a, Eq a) => a -> Bool
isMempty a = a == mempty

type MonoidAndEq a = (Monoid a, Eq a)

-- type Test = Has MonoidAndEq

class (Monoid a, Eq a) => MonoidEq a
instance (Monoid a, Eq a) => MonoidEq a

type Test = Has MonoidEq
