{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.List (intercalate)
import GHC.Exts (Constraint)

infixr 5 :::

data HList (ts :: [*]) where
    Nil   :: HList '[]
    (:::) :: t -> HList ts -> HList (t ': ts) 


type family Map (f :: a -> b) (xs :: [a]) :: [b]
type instance Map f '[] = '[]
type instance Map f (x ': xs) = f x ': Map f xs

type family Constraints (cs :: [Constraint]) :: Constraint
type instance Constraints '[]       = ()
type instance Constraints (c ': cs) = (c, Constraints cs)

type AllHave (c :: k -> Constraint) (xs :: [k]) = Constraints (Map c xs)

showHList :: AllHave Show xs => HList xs -> [String]
showHList Nil           = []
showHList (x ::: xs)    = (show x) : showHList xs

instance AllHave Show xs => Show (HList xs) where
    show xs = "[" ++ (intercalate "," $ showHList xs) ++ "]"

hList :: HList '[Bool, String, Double, ()]
hList = True ::: "foo" ::: 3.14 ::: () ::: Nil


main :: IO ()
main = do
    print hList






