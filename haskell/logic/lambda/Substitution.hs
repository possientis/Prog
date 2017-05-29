module Substitution
  ( (<-:)
  , (<->)
  ) where

(<-:) :: (Eq v) => v -> v -> (v -> v)
(y <-: x) u
  | u == x    = y
  | otherwise = u

(<->) :: (Eq v) => v -> v -> (v -> v)
(y <-> x) u
  | u == x    = y
  | u == y    = x
  | otherwise = u

