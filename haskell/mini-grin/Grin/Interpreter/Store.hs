module Grin.Interpreter.Store where

import Data.Maybe
import Grin.Pretty
import Data.Map.Strict as M

-- * Store

-- | Store maps addresses to abstract values.
newtype Store a v = Store (M.Map a v)
  deriving (Eq, Ord, Show)

empty :: (Ord a) => Store a v
empty = Store mempty

lookup :: (Ord a) => a -> Store a v-> v
lookup a (Store m) = fromMaybe (error "Store; missing") $ M.lookup a m

insert :: (Ord a) => a -> v -> Store a v -> Store a v
insert a v (Store m) = Store (M.insert a v m)

size :: Store a v -> Int
size (Store m) = M.size m

instance (Ord a, Semigroup v) => Semigroup (Store a v) where
  (Store ma) <> (Store mb) = Store (M.unionWith (<>) ma mb)

instance (Ord a, Monoid v) => Monoid (Store a v) where
  mempty = Store mempty

instance (Pretty a, Pretty v) => Pretty (Store a v) where
  pretty (Store m) = prettyKeyValue (M.toList m)
