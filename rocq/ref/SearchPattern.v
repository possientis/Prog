Require Import Arith.

Import Nat.

SearchPattern (_ + _ = _ + _).

SearchPattern (nat -> bool).

SearchPattern (forall l : list _, _ l l).
SearchPattern (forall k : list _, _ k k).


SearchPattern (?X1 + _ = _ + ?X1).
