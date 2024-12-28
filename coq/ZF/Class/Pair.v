Require Import ZF.Axiom.Pairing.
Require Import ZF.Class.
Require Import ZF.Class.Small.
Require Import ZF.Set.

Definition pair (a b:U) : Class := fun x => x = a \/ x = b.

Proposition PairIsSmall : forall (a b:U),
  Small (pair a b).
Proof.
  apply Pairing.
Qed.
