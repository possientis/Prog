module Profunctor
  ( Profunctor
  , dimap
  , lmap
  , rmap
  ) where

-- Def: We call 'Profunctor' a binary type constructor p for which there
-- exists a map dimap :: (a -> b) -> (c -> d) -> p b c -> p a d

class Profunctor p where
  dimap :: (a -> b) -> (c -> d) -> p b c -> p a d

-- Def: Given a binary constructor p, we call 'transformation from b to c' (relative to p)
-- any value of type p b c.  
--
-- Remark: A Profunctor is therefore a binary constructor p relatively to which 
-- transformations can be composed with usual functions. Denoting the transformation
-- types p b c and p a d as 'b ~> c' and 'a ~> d', then given a map f :: a -> b, a 
-- transformation g :: b ~> c and another map h :: c -> d, we obtain a new tranformation
-- dimap f h g :: a ~> d. This new transformation feels like 'h . g . f' in spirit.
--
-- Remark: Given a profunctor p, we expect the composition of transformation with
-- functions to behave in natural ways. More precisely, given a transformation 
-- g :: b ~> c, composing this transformation with the identity before and after 
-- should have no effect:
--
-- (1) dimap id id g = g
--
-- Furthemore, we expect composition to be associative: if f' :: a' -> a,
-- f :: a -> b, h :: c -> d and h' :: d -> d', informally we should have,
-- h' . (h . g . f) . f' = (h' . h) . g . (f . f') which is:
--
-- (2) dimap f' h' (dimap f h g) = dimap (f . f') (h' . h) g

-- Def: We say that a Profunctor p is 'lawful' whenever equalities (1) and (2) are met
-- for every transformation g and maps f,f',h,h'.
--
-- Lemma: (->) is a Profunctor

instance Profunctor (->) where
  dimap f h g = h . g . f

-- Remark: it feels like the Profunctor (->) is lawful. However, given the lack
-- of formal semantics, lack of formal equality between functions (extensional
-- equality doesn't define equality when values can themselves be functions or have
-- no Eq instance), lack of proof and the possibility of functions throwing errors,
-- We shall abstain from claiming anything here.

-- It is often convenient to 'pre-compose' a transformation with a map.
lmap :: (Profunctor p) => (a -> b) -> p b c -> p a c
lmap f g = dimap f id g

-- Similarly, it may be convenient 'post-compose' a transformation with a map.
rmap :: (Profunctor p) => (c -> d) -> p b c -> p b d
rmap h g = dimap id h g

