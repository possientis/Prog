Declare Scope ZF_Set_Power_scope.
Open    Scope ZF_Set_Power_scope.

Require Import ZF.Class.Power.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.

Definition power (a:U) : U := fromClass (power a) (IsSmall a).

Notation ":P( a )" := (power a)
  (at level 0, no associativity) : ZF_Set_Power_scope.

(* Characterisation of the elements of the power set of a.                      *)
Proposition Charac : forall (a:U),
  forall x, x :< :P(a) <-> x :<=: a.
Proof.
  intros a. apply FromClass.Charac.
Qed.
