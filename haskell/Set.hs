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
  show (Union x y)      = (show x) ++ "U" ++ (show y)

instance Eq Set where
  (==) x y = (subset x y) && (subset y x)

instance Ord Set where
  (<=) x y = subset x y

instance ISet Set where
  empty                   = Empty
  singleton x             = Singleton x
  union x y               = Union x y
  -- 
  -- Definition of <= (inclusion)
  -- 
  -- subset is the key relation on free structure Set
  -- providing a definition of subset which is self-contained
  -- i.e. with no dependencies to either 'belong' or '=='
  -- definition: We call an 'inclusion relation' on the free
  -- algebra (X,0,{},U) an binary relation <= satisfying the
  -- property (i)-(v) below. 
  subset Empty _                      = True  -- (i) 0 <= x forall x
  subset (Singleton x) Empty          = False -- (ii) ¬({x} <= 0) forall x
  -- (iii) {x} <= {y} iff (x <= y) /\ (y <= x)
  subset (Singleton x) (Singleton y)  = (subset x y) && (subset y x)
  -- (iv) {x} <= y U z iff {x} <= y \/ {x} <= z
  subset (Singleton x) (Union y z)    = (subset (Singleton x) y) 
                                      ||(subset (Singleton x) z)
  -- (v) x U y <= z iff (x <= z ) and (y <= z)
  subset (Union x y) z    = (subset x z) && (subset y z)
  -- 
  -- Lemma: an inclusion relation exists and is unique
  --
  -- Such binary relation exists and is unique. Informally, 
  -- it exists because we can define it by the structural
  -- recursion-looking definition below. It is unique because 
  -- axioms (i)-(v) enforce a unique definition at each recursive 
  -- step below: they is only one possible way to define this 
  -- relation. This needs formal mathematical proof. 
  --
  -- Remark:
  -- One of the challenges is to prove that <= is reflexive
  -- and transitive. This seems surprisingly difficult as 
  -- any attempt to use structural induction for a proof
  -- seems to fail. There is a need to show other properties
  -- as well such as xUy == yUx (== being defined as <= and >=)
  -- 0Ux = x and xU(yUz) = (xUy)Uz, etc.
  --
  -- Definition: we define x == y as (x <= y && y <= x)
  --
  -- We do not know anything about == at this stage. One 
  -- succesful application of structural induction is
  -- as follows. We start with a definition:
  --
  -- Definition: We define the map E: X -> P(X) by:
  -- E(0) = 0 (the empty set)
  -- E({x}) = {x} (the singleton)
  -- E(aUb) = E(a)UE(b)
  -- informally, E(x) represents the 'elements' of x 
  -- (which is a subset of X). This is not quite true
  -- of course since various elements of E(x) could
  -- be equivalent with respect to ==. The breakthrough:
  --
  -- Lemma 1: forall x,y:X we have x <= y if and only if:
  -- forall z:E(x) exists z':E(y), z == z'
  --
  -- informally, this says that x is a subset of y iff
  -- every element of x is equivalent to an element of y.
  -- For once, structural induction seems to work. Proof:
  --
  -- x = 0. 0 <= y is always true. forall z:E(0) ... is 
  -- vacuously true. So equivalence is true when x = 0.
  --
  -- x = {x'}. We need to show that {x'} <= y is equivalent
  -- to the fact that forall z:E({x'})={x'}, there is z':E(y)
  -- such that z == z'. So we need to focus on the sub-Lemma
  --
  -- sub-Lemma: {x} <= y <=> exits z:E(y) x == z.
  --
  -- we shall do this by induction on y: 
  -- if y = 0, both sides of equivalence are always false.
  -- if y = {y'}. we need to show the equivalence
  -- {x} <= {y'} <=> x == y' which follows from property (iii)
  -- of the definition of <=.
  -- we now assume that y=aUb where a and b satisfy the induction
  -- hypothesis. We need to show {x} <= aUb <=> exists z:E(a)UE(b)
  -- such that x == z. From the induction hypothesis, we see that
  -- {x} <= a is equivalent to exists z:E(a) x == z, and similarly
  -- for b. So we need to show the equivalence {x} <= aUb <=>
  -- {x} <= a || {x} <= b  which is true by virtue of property 
  -- (iv) of the definition of <=. This completes the proof
  -- of the sub-lemma and the case x = {x'} of the lemma.
  --
  -- x = aUb, where a and b satisfy the induction hypothesis.
  -- we need to show that aUb <= y is equivalent to 
  -- for all z:E(a)UE(b) there is z':E(y), z == z'.
  -- However, from the induction hypothesis we see that
  -- a <= y is equivalent to forall z:E(a) there is z':E(y), 
  -- z == z', and similarly for b. So we have to prove the 
  -- equivalence aUb <= y <=> a <= y && b <= y which is true 
  -- from (v) of the definition of <=. This completes the proof.
  --
  -- Definition: we define order: X -> N as follows:
  -- order(0) = 1
  -- order({x}) = 1 + order(x)
  -- order(xUy) = 1 + max(order(x), order(y))
  --
  -- Lemma 2: forall x:X and z:E(x), order(z) < order(x)
  --
  -- by induction on x. If x = 0, E(0) is empty and the property
  -- is vacuously true. if x = {x'} then z:E(x) is z=x' and we
  -- have order(x') < order(x) by definition of order.
  -- if x = aUb where a, b satisfy the induction hypothesis and
  -- if z:E(x), then z:E(a) or z:E(b). in the first case, from
  -- the induction hypothesis we obtain order(z) < order(a)
  -- and in the second case order(z) < order(b). The result follows
  -- from order(a), order(b) < order(x).
  --
  -- We are now able to handle reflexivity of <=.
  --
  -- Lemma 3: the relation <= on X is reflexive
  --
  -- We proceed to prove x <= x by induction on order(x).
  -- If order(x) = 1, then x can only be 0 and 0 <= 0 is true.
  -- We assume the property is true for order(x) <= N >=1
  -- We need to show it is true for order(x) <= N+1. We 
  -- may assume that order(x) = N+1. We need to show that
  -- x <= x. Using Lemma 1, it is sufficient to show that
  -- for all z:E(x) we have z == z (which is z <= z).
  -- However from Lemma 2 we see that any such z is such that
  -- order(z) < order(x). In particular, order(z) <= N and the
  -- property z <= z follows from the induction hypothesis.
  --
  -- Lemma 4: forall x y:X, x <= xUy
  --
  -- Applying Lemma 1, it is sufficient to show that for all
  -- z:E(x) there is z':E(x)UE(y), z == z'. Hence it is 
  -- sufficient to prove that z == z for all z:E(x), which
  -- we know is true by reflexivity of Lemma 3.
  --
  -- Lemma 5: forall x y:X, xUy == yUx
  --
  -- Also follows immediately from Lemma 1 and reflexivity
  --
  -- Lemma 6: forall x y z:X, (xUy)Uz == xU(yUz)
  --
  -- idem
  --
  -- Lemma 7: forall x:X, xU0 == x
  --
  -- idem
  --
  -- And now the big prize:
  --
  -- Lemma 8: the relation <= on X is transitive
  --
  -- We shall prove the implication (x <= y)/\(y <= z) -> (x <= z)
  -- by induction on the maximum order of x, y and z. If the order
  -- of x,y,z are all less than 1, then x = y = z = 0 and the
  -- property is true. So we assume that the property is true
  -- whenever the orders of x,y,z are all less than (or equal to) N.
  -- We need to show the property is true whenever the orders
  -- of x,y,z are all less than N+1 (or equal). So let's assume this is the 
  -- case and that x <= y together with y <= z. We need to show that
  -- x <= z. Using Lemma 1, given u:E(x) we need to show the 
  -- existence of w:E(z) such that u == w. However from x <= y
  -- there exists v:E(y) such that u == v, and from y <= z, 
  -- there exists w:E(z) such that v == w. However, from Lemma 2
  -- the orders of u,v,w are all less than (or equal to) N. From 
  -- the induction hypothesis, u == v and v == w we can conclude
  -- that u == w which completes the proof of the lemma.
  --
  -- Lemma 9: the relation == on X is a congruence.
  --
  -- First we show it is an equivalence relation. Being defined
  -- as x == y iff (x <= y)/\(y <= x), it is clearly symmetric.
  -- Furthermore, it is reflexive from Lemma 3 and transitive
  -- from Lemma 8. We now show that == is compatible with the
  -- operators of the free algebra (X, 0, {}, U). We have 0 == 0.
  -- We assume that x == y. We need to show that {x} == {y}. This
  -- follows immediately from (iii) of the definition of <= 
  -- which states that {x} <= {y} is equivalent to x == y.
  -- We know assume that x == x' and y == y'. We need to show 
  -- that xUy == x'Uy'. It is sufficient to prove that 
  -- xUy <= x'Uy' follows from x <= x' and y <= y'. Using (v)
  -- of the definition of <=, it is sufficient to prove that 
  -- x <= x'Uy' and y <= x'Uy', and since xUy commutes modulo 
  -- == (by Lemma 5), it is sufficient to establish the following
  --
  -- Lemma 10: for all x x' y:X, if x <= x' then xUy <= x'Uy 
  -- Applying Lemma 1, given z in E(xUy) = E(x)UE(y), we need
  -- to show the existence of z' in E(x')UE(y) such that 
  -- z == z' If z is in E(y) we can take z'=z and we are done
  -- since == is reflexive. If z is in E(x), from x <= x' we 
  -- obtain the existence of z' in E(x') such that z == z'. So 
  -- we are also done in this case.
  --
  --
  -- Lemma 11: The relation <= on X is compatible with ==.
  -- That is if x == x' and y == y' and x <= y, then we 
  -- must have x' <= y'. This follows immediately from
  -- the transitivity of <= (Lemma 8)
  --
  --
  -- Definition: We can now define the quotient space X/==
  -- which will shall denote X* or (X*,0, {}, U), on which
  -- the inclusion <= is well defined (Lemma 11).
  --
  -- Lemma 12: for all x y:X* we have x=y iff (x<=y)/\(y<=x)
  -- This seems pretty obvious, let us make sure we get it
  -- formally right. For the purpose of the proof, given 
  -- x y in X, we denote [x] and [y] the elements of X* 
  -- representing the classes of x and y modulo == respectively.
  -- we need to show that [x]=[y] iff ([x]<=[y])/\([y]<=[x]).
  -- but [x]=[y] is equivalent to x == y and [x]<=[y] is (by
  -- definition) equivalent to x <= y. So we are done.
  --
  -- Lemma 13: The relation <= on X* is a partial order.
  -- Since [x]<=[y] is defined as x<=y (definition which is
  -- legitimate by Lemma 11), we immediately see that <=
  -- is reflexive and transitive. It remains to show that
  -- it is also symmetric. But [x]<=[y] and [y]<=[x] imply
  -- that x == y and consequently [x]=[y].
  --
  -- Just like we did for X we can define for X* the notion
  -- of a 'set's elements':
  --
  -- Definition: We define the map E*: X* -> P(X*) by:
  -- E([0])   = 0         (the empty set) 
  -- E({[x]}) = {[x]}     (the singleton)
  -- E([a]U[b])   = E([a])UE([b]) (the union)
  --
  -- Warning: beware that given x in X or X*, the notation {x}
  -- is ambiguous (overloaded), as it may refer to the set
  -- theoretic singleton {x} (set with unique element x) or to the 
  -- value obtainied by applying the unary operator {} on x.
  --
  -- contrary to natural belief, it seems that the inclusion
  -- relation is more primitive that the 'belong' relation.
  belong x y = subset (Singleton x) y


zero  = set 0 :: Set
one   = inc zero 
two   = inc one
three = inc two
four  = inc three
five  = inc four

generate :: ISet a =>  Int -> [a]
generate 0 = [empty]
generate n = let prior = generate (n-1) in
  prior ++ [(singleton x) | x <- prior] ++ [(union x y) | x <- prior, y <- prior]

check1 :: Int -> (Set -> Bool) -> Bool
check1 n p = all p (generate n)

check2 :: Int -> (Set->Set->Bool)->Bool
check2 n p = and [p x y | x <- list, y <- list] where list = generate n

check3 :: Int -> (Set->Set->Set->Bool)->Bool
check3 n p = and [p x y z | x <- list, y <- list, z <- list] 
  where list = generate n