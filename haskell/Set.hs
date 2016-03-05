module Set (ISet, empty, set, inc, belong, singleton, union, subset, Set) where

class ISet a where
  empty     :: a
  singleton :: a -> a
  union     :: a -> a -> a
  belong    :: a -> a -> Bool
  subset    :: a -> a -> Bool
  -- successor
  inc       :: a -> a
  inc x                   = union x (singleton x)
  -- Embedding for natural numbers
  set       :: Int -> a
  set 0                   = empty
  set x                   = inc (set (x - 1))

class IFree a where -- free structures, aka ADT
  order :: a -> Int

data Set = Empty | Singleton Set | Union Set Set

instance IFree Set where
  order Empty         = 1
  order (Singleton x) = 1 + order x
  order (Union x y)   = 1 + max (order x) (order y)

instance Show Set where
  show Empty            = "0"
  show (Singleton x)    = "{"++(show x)++"}"
  show (Union Empty y)  = show y
  show (Union x Empty)  = show x
  show (Union x y)      = (init (show x))++","++(drop 1 (show y))

instance Eq Set where
  (==) x y = (subset x y) && (subset y x)

instance Ord Set where
  (<=) x y = subset x y

instance ISet Set where
  empty                   = Empty
  singleton x             = Singleton x
  union x y               = Union x y
  -- subset is the key relation on free structure Set
  -- providing a definition of subset which is self-contained
  -- i.e. with no dependencies to either 'belong' or '=='
  -- definition: We call an 'inclusion relation' on the free
  -- algebra (X,0,{},U) an binary relation <= satisfying the
  -- property (i)-(v) below. Such binary relation exists and
  -- is unique. Informally, it exists because we can define
  -- it by the structural-recursion-looking definition below.
  -- It is unique because axioms (i)-(v) enforce a unique
  -- definition at each recursive step below: they is only one 
  -- possible way to define this reltion. This needs formal
  -- mathematical proof. 
  subset Empty _                      = True  -- (i) 0 <= x forall x
  subset (Singleton x) Empty          = False -- (ii) ¬({x} <= 0) forall x
  -- (iii) {x} <= {y} iff (x <= y) /\ (y <= x)
  subset (Singleton x) (Singleton y)  = (subset x y) && (subset y x)
  -- (iv) {x} <= y U z iff {x} <= y \/ {x} <= z
  subset (Singleton x) (Union y z)    = (subset (Singleton x) y) 
                                      ||(subset (Singleton x) z)
  -- (v) x U y <= z iff (x <= z ) and (y <= z)
  subset (Union x y) z    = (subset x z) && (subset y z)
  -- contrary to natural belief, it seems that the inclusion
  -- relation is more primitive that the 'belong' relation.
  belong x y = subset (Singleton x) y


zero  = set 0 :: Set
one   = inc zero 
two   = inc one
three = inc two
four  = inc three
five  = inc four



