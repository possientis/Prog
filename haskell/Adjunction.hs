{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE LambdaCase         #-}

module Adjunction where

import Prelude hiding (Functor (..), product,maybe)

import Data.Kind


-- * categories

data Category (c :: Type -> Type -> Type) = Category 
    { src :: forall x y . c x y -> c x x
    , tgt :: forall x y . c x y -> c y y 
    , cmp :: forall x y z . c y z -> c x y -> c x z
    }

type Hask = (->)

hask :: Category Hask
hask  = Category
    { src = \_ -> id  
    , tgt = \_ -> id
    , cmp = (.) 
    }

newtype SubHask (f :: Type -> Type) (a :: Type) (b :: Type) = SH (a -> b)

subCategory :: Category (SubHask f)
subCategory = Category
    { src = \_ -> SH id
    , tgt = \_ -> SH id
    , cmp = \(SH g) (SH f) -> SH (g . f) 
    }


newtype Op (c :: Type -> Type -> Type) a b = Op (c b a)

op :: Category c -> Category (Op c) 
op c1 = Category
    { src = \(Op f) -> Op (tgt c1 f)
    , tgt = \(Op f) -> Op (src c1 f)
    , cmp = \(Op g) (Op f) -> Op (cmp c1 f g)
    } 

data Product (c1 :: Type -> Type -> Type) (c2 :: Type -> Type -> Type) a b where
    Product :: (c1 a1 b1) -> (c2 a2 b2) -> Product c1 c2 (a1,a2) (b1,b2)

product :: Category c1 -> Category c2 -> Category (Product c1 c2)
product c1 c2 = Category
    { src = \(Product f1 f2) -> Product (src c1 f1) (src c2 f2)
    , tgt = \(Product f1 f2) -> Product (tgt c1 f1) (tgt c2 f2)
    , cmp = \(Product g1 g2) (Product f1 f2) -> Product (cmp c1 g1 f1)(cmp c2 g2 f2)
    }



-- * Functor

{-
type family FunctorT (f :: Type -> Type) (t :: Type) :: Type

data Functor (f :: Type -> Type) c1 c2 = Functor
    { fmap  :: forall x1 y1 x2 y2 
            .  (FunctorT f x1 ~ x2, FunctorT f y1 ~ y2) 
            => c1 x1 y1 -> c2 x2 y2
    }
-}


data Functor (f :: Type -> Type) c1 c2 = Functor
    { fmap :: forall x y . c1 x y -> c2 (f x) (f y)
    }

maybe :: Functor Maybe Hask Hask
maybe  = Functor
    { fmap = \f -> \case
        Nothing -> Nothing
        Just x  -> Just (f x)
    }

maybe' :: Functor Maybe Hask (SubHask Maybe)
maybe'  = Functor
    { fmap = \f -> SH $ \case
        Nothing -> Nothing
        Just x  -> Just (f x)
    }

newtype Diag a = Diag (a,a)

{-
diag :: Functor Diag Hask (Product Hask Hask)
diag = Functor
    { fmap = \f -> a
    }
-}
