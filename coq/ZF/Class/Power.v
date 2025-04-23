Require Import ZF.Axiom.Power.
Require Import ZF.Class.Core.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.

Definition power (a:U) : Class := fun x => x :<=: a.

(* The power class of the set a is small.                                       *)
Proposition PowerIsSmall : forall (a:U), Small (power a).
Proof.
  apply Power.
Qed.
