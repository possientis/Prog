{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

import Data.Foldable
import Control.Monad.State

data Traversed t a = Traversed { shape :: t (), contents :: [a] }


break :: (Functor t, Foldable t) => t a -> Traversed t a
break ta = Traversed (fmap (const ()) ta) (toList ta)


pop :: State [a] a
pop = state $ \(a:as) -> (a, as)


recombine :: Traversable t => Traversed t a -> t a
recombine (Traversed s c) = evalState (traverse (const pop) s) c


deriving instance (Functor t) => Functor (Traversed t)
deriving instance (Functor t, Foldable t) => Foldable (Traversed t)


instance (Functor t, Foldable t) => Traversable (Traversed t) where
    traverse f (Traversed s c) = fmap (Traversed s) (traverse f c)
