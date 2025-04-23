Require Import ZF.Axiom.Pairing.
Require Import ZF.Class.Core.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.

(* The class of all sets x which are equal to a or equal to b.                  *)
Definition pair (a b:U) : Class := fun x => x = a \/ x = b.

(* The Pairing axiom ensures this is a small class.                             *)
Proposition PairIsSmall : forall (a b:U),
  Small (pair a b).
Proof.
  apply Pairing.
Qed.
