import Data.Foldable
import Data.Map


-- foldMap :: Monoid m => (a -> m) -> t a -> m

data    Elt
    =   Elt Int Double
    |   Nil

foo :: [Elt] -> Map Int Double
foo xs = foldMap go xs where
    go :: Elt -> Map Int Double
    go (Elt x y) = singleton x y
    go Nil       = empty


data List a = Nil' | Cons' a (List a)

instance Foldable List where
    foldMap f Nil'          = mempty
    foldMap f (Cons' x xs)  = f x `mappend` foldMap f xs


newtype Endo a = Endo { appEndo :: a -> a }

instance Monoid (Endo a) where
    mempty = Endo id
    Endo f `mappend` Endo g = Endo (f . g)

