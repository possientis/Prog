{-# LANGUAGE DeriveFunctor #-}

module Grin.Interpreter.Env where

import Data.List        as L
import Data.Maybe
import Data.Map.Strict  as M

import Grin.Pretty
import Grin.Value

-- * Env

-- | Environment mapping names to abstract values.
newtype Env v = Env (M.Map Name v)
  deriving (Eq, Show, Ord, Functor)

empty :: Env v
empty  = Env mempty

lookup :: (Env v) -> Name -> v
lookup (Env m) n = fromMaybe (error $ "Missing:" ++ show n) $ M.lookup n m

insert :: Name -> v -> Env v -> Env v
insert n v (Env m) = Env $ M.insert n v m

inserts :: [(Name, v)] -> Env v -> Env v
inserts vs (Env m) = Env $ L.foldl' (\n (k,v) -> M.insert k v n) m vs

-- Explicit instance!! different from default
instance (Semigroup v) => Semigroup (Env v) where
  Env m1 <> Env m2 = Env (M.unionWith (<>) m1 m2)

instance (Semigroup v) => Monoid (Env v) where
  mempty = Env mempty

instance (Pretty v) => Pretty (Env v) where
  pretty (Env m) = prettyKeyValue (M.toList m)
