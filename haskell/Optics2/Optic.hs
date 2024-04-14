module Optic
  ( Optic
  ) where

-- Def: given a binary type constructor p, and types s t a b, we call 'optic'
-- (relative to p s t a b) any functions between transformations of type a ~> b
-- to transformations of type s ~> t.
type Optic p s t a b = p a b -> p s t
