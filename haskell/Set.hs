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
  order :: a -> Integer

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
  -- Lemma 0: an inclusion relation exists and is unique
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
  -- 
  -- Applying Lemma 1, given z in E(xUy) = E(x)UE(y), we need
  -- to show the existence of z' in E(x')UE(y) such that 
  -- z == z' If z is in E(y) we can take z'=z and we are done
  -- since == is reflexive. If z is in E(x), from x <= x' we 
  -- obtain the existence of z' in E(x') such that z == z'. So 
  -- we are also done in this case.
  --
  --
  -- Lemma 11: The relation <= on X is compatible with ==.
  --
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
  --
  -- This seems pretty obvious, let us make sure we get it
  -- formally right. For the purpose of the proof, given 
  -- x y in X, we denote [x] and [y] the elements of X* 
  -- representing the classes of x and y modulo == respectively.
  -- we need to show that [x]=[y] iff ([x]<=[y])/\([y]<=[x]).
  -- but [x]=[y] is equivalent to x == y and [x]<=[y] is (by
  -- definition) equivalent to x <= y. So we are done.
  --
  -- Lemma 13: The relation <= on X* is a partial order.
  --
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
  -- E*([0])   = 0         (the empty set) 
  -- E*({[x]}) = {[x]}     (the singleton)
  -- E*([a]U[b])   = E*([a])UE*([b]) (the union)
  --
  -- Warning: beware that given x in X or X*, the notation {x}
  -- is ambiguous (overloaded), as it may refer to the set
  -- theoretic singleton {x} (set with unique element x) or to the 
  -- value obtainied by applying the unary operator {} on x.
  --
  -- There is a natural relationship between E* and E:
  --
  -- Lemma 14: forall x:X, E*([x]) = { [y] | y:E[x] } 
  -- 
  -- Proof by structural induction.
  --
  -- In other words the elements of the class of x, are
  -- the classes of the elements of x.
  --
  -- Definition: given x y:X we say that x belongs to y,
  -- denoted x in y or x:y, if and only {x} <= y.

  belong x y = subset (Singleton x) y

  -- Lemma 15: the 'belong' (':' , 'in') relation on X
  -- is compatible with the congruence == on X, in other
  -- words, if x == x' and y == y' and x:y, then x':y'
  --
  -- Proof: we need to show that {x'} <= y', but == being
  -- a congruence we have {x'} == {x} and the result follows
  -- immediately by transitivity.
  --
  -- We can therefore extend the relation belong to the 
  -- quotient algebra X* by defining [x]:[y] iff x:y.
  --
  -- We now have the interesting lemma:
  --
  -- Lemma 16: for all x y:X*, x:y <=> x:E*(y)
  --
  -- Be careful that the above 'x:y' refers to the quotient
  -- binary relation ':' on X*, while 'x:E*(y)' refers to the
  -- usual set theoretic 'x is an element of the set E*(y)'.
  -- The set E*(y) is supposed to represents of the elements
  -- of X* which are 'element' of y. So Lemma 16 should be
  -- true, or something is wrong with the whole thing, or
  -- with the definition of ':' or with that of E*.
  --
  -- Proof: in order to be totally formal, we shall keep
  -- the notations [x] and [y] to distinguish elements of X
  -- from their corresponding classes in X*.
  --
  -- We need to show that [x]:[y] <=> [x]:E*([y]). However,
  -- [x]:[y] is defined as x:y which is itself defined 
  -- as {x} <= y. By Lemma 1, this is equivalent to the fact
  -- for all z in E({x}) = {x}, there should be z' in E(y)
  -- such that z == z'. In brief, [x]:[y] is equivalent 
  -- to the existence of z in E(y) such that x == z.
  -- Now from lemma 14, [x]:E*([y]) is equivalent to 
  -- [x] = [z] for some z in E(y). Hence it is also equivalent
  -- to the existence of z in E(y) such that x == z. We done.
  --
  -- Lemma 17: forall x y:X*, x <= y <=> E*(x) <= E*(y)
  -- 
  -- (E*(x) <= E*(y) refers to the usual set theoretic inclusion)
  -- Formally given x y:X we need to show that [x] <= [y] (which
  -- is equivalent to x <= y) is equivalent to E*([x]) <= E*([y]).
  -- First we prove =>. So we assume that x <= y, and we assume
  -- that [z] in E*([x]). We need to show that [z] in E*([y]).
  -- From Lemma 14, there is z1 in E(x) such that z == z1. 
  -- However from Lemma 1 and x <= y, there is z2 in E(y)
  -- such that z1 == z2. Hence by transitivity, there is z2 
  -- in E(y) such that z == z2. This shows from Lemma 14 that
  -- [z] in E*([y]) as requested. We now prove <=. So we assume
  -- that the inclusion E*([x]) <= E*([y]) holds and we need to
  -- show that x <= y. We shall use Lemma 1 so we assume that
  -- z in E(x). We need to show the existence of z' in E(y) 
  -- such that z == z' However from z in E(x) and Lemma 14 we obtain
  -- [z] in E*([x]) and from the assumed inclusion it follows that
  -- [z] in E*([y]). Using Lemma 14 once again, we see that 
  -- z == z' for some z' in E(y), we completes the proof.
  --
  --
  --Lemma 18: forall x y:X*, we have the equivalence:
  --  x <= y  <=> forall z:X*, z:x -> z:y
  --
  -- In other words, on the quotient algebra X*, the binary 
  -- relation <= truly behaves as in inclusion relation with
  -- respect to the belong relation ':', which is what we want.
  --
  -- Proof: 
  -- By virtue of Lemma 17, x <= y is equivalent to the
  -- inclusion E*(x) <= E*(y). However, from Lemma 16,
  -- given z:X*, z:x is equivalent to z:E*(x). Hence 
  -- we have to prove that the inclusion is equivalent to
  --  forall z:X*, z:E*(x) -> z:E*(y)
  -- which is indeed the case. 
  --
  -- Somehow we feel that an element of X* refers to a real set
  -- in the world of ZF. We are tempted to define a map F with 
  -- domain X* by the following structural recursion:
  --
  --  (i)   F(0) = 0              (the empty set)
  --  (ii)  F({x}) = {F(x)}       (the set with one element)
  --  (iii) F(xUy) = F(x)UF(y)    (the usual set theoretic union)
  --
  -- Remark: we dropped the formal notation [x] in the previous
  -- definition, so 0 here denotes the element [0] of X* etc
  --
  -- but this would be a gross mistake as structural induction
  -- definition are only legitimate for free algebras. So we shall
  -- define F on X instead and show it is compatible with ==.
  --
  -- Definition: we define the map F with domain X as follows:
  --
  --  (i)   F(0) = 0              (the empty set)
  --  (ii)  F({x}) = {F(x)}       (the set with one element)
  --  (iii) F(xUy) = F(x)UF(y)    (the usual set theoretic union)
  --
  -- Remark: The formal justification of the existence of the
  -- map F from the axioms of ZF is required. This is a slightly
  -- more difficult case than usual as we do not have an obvious
  -- set to work with as the range of F.
  --
  -- Remark: do not confuse F(x) with E(x) eventhough the 
  -- definitions of F and E are very similar. Given x:X,
  -- E(x) is a subset of X. It is a set of formal expression.
  -- F(x) is not a subset of X. It is simply a set which is
  -- the value of the expression x in the world of sets. For 
  -- example, if we consider the element 1 = {0} of X. It is a
  -- formal expression, and F(1) = 1 (the set theoretic singleton 
  -- {0}). We have E(1) = {0}, the singleton containing the element 
  -- 0 of X.
  -- 
  -- Remark: With a bit of work, using the ZF axiom schema of
  -- replacement, we should be about to justify the fact that
  -- the range F(X) is a well defined set. Hence we have a
  -- map F: X -> F(X). This map is compatible with ==.
  --
  -- Lemma 19: forall x:X, F(x) = { F(z) | z:E(x) }
  --
  -- Proof: by structural induction. Since both F(0) and E(0)
  -- are empty sets, the equality is true when x = 0. Since
  -- F({x})={F(x)} (the singleton with unique element F(x)),
  -- and E({x}) = {x} (the singleton with unique element x:X),
  -- the equality is true in the case {x}. So we assume that
  -- x = aUb where a b:X are such that the equality is true.
  -- We need to show it is also true for x:
  --
  -- F(x) = F(aUb) = F(a)UF(b) = {F(z)|z:E(a)}U{F(z):z:E(b)}
  --      = {F(z)|z:E(a)UE(b)} = {F(z)|z:E(x)} 
  -- so we are done.
  --
  -- Lemma 20: The map F: X -> F(x) is compatible with ==, i.e.
  -- for all x y:X we have have the implication:
  --
  --            x == y -> F(x) = F(y)
  -- 
  -- Proof: by induction on the order of x and y. If both the
  -- order of x and y are 1, then x = y = 0 and the implication
  -- is clearly true. So we assume the implication is true
  -- whenever both the order of x and y are <= N (for N>= 1).
  -- We need to show the implication is also true whenever
  -- x and y have orders <= N+1. So let us assume this is the
  -- case and furthermore that x == y. We need to show that
  -- F(x) = F(y). First we show the inclusion F(x) <= F(y).
  -- Given u in F(x), we need to show that u:F(y). However
  -- by Lemma 19, u = F(z) for some z:E(x). From the assumption
  -- x == y, in particular we have x <= y, and using Lemma 1
  -- together with z:E(x), we see that there exists z' in E(y)
  -- such that z == z'. From Lemma 2, order(z) < order(x) and
  -- order(z') < order(y). It follows that both the orders of
  -- z and z' are <= N. From our induction hypothesis together
  -- with z == z', we obtain F(z) = F(z'). Hence we see that
  -- u = F(z') for some z':E(y). We conclude from Lemma 19 that
  -- u belongs to F(y) which completes the proof of F(x) <= F(y).
  -- The proof of F(y) <= F(x) is handled identically. 
  --
  -- We are now able to define F on the domain X* rather than X
  --
  -- Definition: we can define F*:X* -> F(X) by F([x]) = F(x)
  --
  -- By Lemma 20, this definition is legitimate.
  --
  -- Lemma 21: forall x y:X*, we have:
  --
  --  (i)   F*(0) = 0               (the empty set)
  --  (ii)  F*({x}) = {F*(x)}       (the set with one element)
  --  (iii) F*(xUy) = F*(x)UF*(y)   (the usual set theoretic union)
  --
  -- Remark: in (i), it is understood that the LHS '0' refers to
  -- the element [0] of X*, namely the equivalence class of 0 mod ==
  --
  -- Proof: F*([0]) = F(0) = 0
  --        F*({[x]}) = F*([{x}]) = F({x}) = {F(x)} = {F*([x])}
  --        F*([x]U[y]) = F*([xUy]) = F(xUy) = F(x)UF(y) = F*([x])UF*([y])
  --
  -- Lemma 22: the map F*: X* -> F*(X*)=F(X) is a bijection
  --
  -- So this is like saying that we have defined a universe of
  -- sets F(X), for which we have an exact representation as
  -- and algebraic data type (except maybe that algebraic data
  -- type corresponds to the notion of free universal algebra,
  -- and our algebra X* is not free, as it is a quotient algebra). 
  --
  -- Proof: we need to show the implication for all x y:X*,
  --   F*(x) = F*(y) -> x = y
  -- or equivalently that for all x y:X,
  --  F(x) = F(y) -> x == y
  -- which is the reverse implication as that of Lemma 20.
  -- We shall prove this implication by induction of the order
  -- of x and y in similar fashion to what was done for Lemma 20
  -- if the order of x and y is 1, then x = y = 0 and the implication
  -- is clearly true. So we assume the implication is true whenever
  -- the order of x and y are both <= N. We need to show it is still
  -- true whenever the order of x and y are both <= N+1. So we assume
  -- the is the case and furthermore that F(x) = F(y). We need to 
  -- show that x == y. First we show that x <= y. Using Lemma 1,
  -- given z:E(x) we need to show the existence of z':E(y) such that
  -- z == z'. However from Lemma 19 and z:E(x) we see that F(z):F(x).
  -- Hence, from the assumption F(x)=F(y) we see that F(z):F(y) and
  -- applying Lemma 19 once more, F(z)=F(z') for some z':E(y). It 
  -- remains to show that z == z'. However from Lemma 2 we have 
  -- order(z) < order(x) and order(z') < order(y). So both the 
  -- order of z and z' are <= N and we have F(z)=F(z'). From our
  -- induction hypothesis it follows that z == z' which completes
  -- the proof of x <= y. The proof of y <= x is identical. 
  --
  -- In fact, given Lemma 21 and Lemma 22, F*: X* -> F(X) is an
  -- isomorphism between the algebras (X*,0,{},U) and (F(X),0,{},U),
  -- where 0, {}, U on F(X) are the usual set-theoretic operators
  -- (F(X) is clearly closed for those operators) 
  --
  -- It is quite nice that we have an algebra of sets (F(X),0,{},U)
  -- which is a mathematical object, which is isomorphic to another
  -- algebra (X*,0,{},U) (another mathematical object), where the
  -- latter has an obvious computing representation as an algebraic
  -- data type modulo the equivalence ==.
  --

  -- We now need to introduce a new notion which is similar to that
  -- of 'order' but different. We call it 'rank'
  --
  -- Definition: we define rnk: X -> N by induction:
  -- rnk(0)   = 0
  -- rnk({x}) = 1 + rnk(x)
  -- rnk(aUb) = 1 + max(rnk(a),rnk(b))

rank :: Set -> Integer
rank Empty          = 1
rank (Singleton x)  = 1 + rank x
rank (Union x y)    = max (rank x) (rank y)

  -- Lemma 23: for all x:X we have:
  --
  --  rnk(x) = max{ 1 + rnk(z) | z:E(x) }
  --
  -- with the convention that max(0) = 0 
  -- Proof: by structural induction. Since E(0) = 0 and max(0) = 0
  -- the property is true for x = 0. Since E({x}) = {x}, it is also
  -- clearly true for {x}. We now assume that x=aUb where a b:X are
  -- such that the equality is true. Then we have:
  --
  -- rnk(x) = max(rnk(a),rnk(b))
  --        = max(max{1+rnk(z)|z:E(a)}, max{1+rnk(z)|z:E(b)})
  --        = max{1+rnk(z)|z:E(a)UE(b)}
  --        = max{1+rnk(z)|z:E(x)}
  -- This completes the proof of the lemma.
  --
  -- The rank is an interesting notion because it is compatible with
  -- the congruence ==, contrary to the notion of order:
  --
  -- Lemma 24: forall x y:X we have the implication:
  --
  --  x == y  -> rnk(x) = rnk(y)
  --
  -- Proof: We shall prove this result by induction on the rank of 
  -- x and y. First we assume that the rank of x and y is 0. Then
  -- the implication is clearly true. So we assume that the implication
  -- is true whenever x and y have rank <= N for a given N>=1. We need
  -- to show that it is still true whenever the rank of x and y are 
  -- <= N+1. so we assume this is the case and furthermore that 
  -- x == y. We need to show that rnk(x) = rnk(y). However let z:E(x).
  -- Since x == y, in particular x <= y and by Lemma 1 there exists
  -- z':E(y) such that z == z'. However by Lemma 23, we see that the
  -- rnk(z) < rnk(x) and rnk(z') < rnk(y). It follows that both the
  -- rank of z and z' are <= N. From z == z' and the induction hypothesis
  -- we obtain rnk(z) = rnk(z'). Hence from Lemma 23 we have:
  --  1 + rnk(z) = 1 + rnk('z) <= rnk(y)
  -- This being true for all z:E(x), we conclude that rnk(x)<=rnk(y).
  -- We prove similarly that rnk(y) <= rnk(x).

  -- Thanks to Lemma 24, the notion of rank can be extended to the
  -- quotient algebra X* with the following definition:
  --
  -- Definition: we define rnk* : X* -> N by setting rnk*([x]) = rnk(x).
  --
  --
 
zero      = set 0 :: Set
one       = inc zero 
two       = inc one
three     = inc two
four      = inc three
five      = inc four
six       = inc five
seven     = inc six
eight     = inc seven
nine      = inc eight
ten       = inc nine
eleven    = inc ten
twelve    = inc eleven

-- worse case computational complexity of computing (x <= y)
complexity :: Set -> Set -> Integer
complexity Empty _                      = 1
complexity (Singleton _) Empty          = 1
complexity (Singleton x) (Singleton y)  = complexity x y + complexity y x
complexity (Singleton x) (Union y z)    = complexity (Singleton x) y + complexity (Singleton x) z
complexity (Union x y) z                = complexity x z + complexity y z






