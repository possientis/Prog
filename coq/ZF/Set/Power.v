Declare Scope ZF_Set_Power_scope.
Open    Scope ZF_Set_Power_scope.

Require Import ZF.Class.Power.
Require Import ZF.Core.Leq.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.

Definition power (a:U) : U := fromClass (Class.Power.power a)
  (PowerIsSmall a).

Notation ":P( a )" := (power a)
  (at level 0, no associativity) : ZF_Set_Power_scope.

(* Characterisation of the elements of the power set of a.                      *)
Proposition PowerCharac : forall (a:U),
  forall x, x :< :P(a) <-> x :<=: a.
Proof.
  intros a. apply FromClassCharac.
Qed.
