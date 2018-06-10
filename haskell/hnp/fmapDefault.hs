import Data.Traversable


instance (Traversable a) => (Functor a) where
    fmap = fmapDefault

