Declare Scope Church_scope.
Open    Scope Church_scope.

Definition CNat : Type := forall (X:Type) (f:X -> X), X -> X.

Notation ":N:" := CNat
  (at level 0, no associativity) : Church_scope.

Definition zero : :N: := fun X f x => x.

Notation ":0:" := zero
  (at level 0, no associativity) : Church_scope.

Definition S (n : :N:) : :N: := fun X f x => f (n X f x).

(* Definining 1 in the most natutal and easy way.                               *)
Definition one : :N: := S :0:.

Notation ":1:" := one
  (at level 0, no associativity) : Church_scope.

(* Computing the normal form of 1.                                              *)
Eval compute in :1:.

(* Checking equality between 1 and its normal form.                             *)
Proposition NormalForm1 : :1: = fun X f x => f x.
Proof. reflexivity. Qed.

Definition two  : :N: := S :1:.

Notation ":2:" := two
  (at level 0, no associativity) : Church_scope.

Proposition NormalForm2 : :2: = fun X f x => f (f x).
Proof. reflexivity. Qed.

Definition three: :N: := S :2:.

Notation ":3:" := three
  (at level 0, no associativity) : Church_scope.

Proposition NormalForm3 : :3: = fun X f x => f (f (f x)).
Proof. reflexivity. Qed.

(* n + m is S applied n times to m: n + m = S (S .. (S m).                      *)
(* However, this intuition when formalised leads to a universe inconsistency.   *)
Fail Definition plus (n m : :N:) : :N: := n (:N: -> :N:) S m.

Definition plus (n m : :N:) : :N: := fun X f x => n X f (m X f x).

