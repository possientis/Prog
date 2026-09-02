Declare Scope ZF_Set_Power_scope.
Open    Scope ZF_Set_Power_scope.

Require Import ZF.Class.Power.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Single.

Definition power (a:U) : U := fromClass (power a) (IsSmall a).

Notation ":P( a )" := (power a)
  (at level 0, no associativity) : ZF_Set_Power_scope.

(* Characterisation of the elements of the power set of a.                      *)
Proposition Charac : forall (a:U),
  forall x, x :< :P(a) <-> x :<=: a.
Proof.
  intros a. apply FromClass.Charac.
Qed.

(* Every set belongs to its own power set.                                      *)
Proposition IsIn : forall (a:U), a :< :P(a).
Proof.
  intros a. apply Charac, Incl.Refl.
Qed.

(* The power set of the empty set is the singleton containing the empty set.    *)
Proposition WhenZero : :P(:0:) = :{:0:}:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Incl.Double. split; intros x H1.
  - (* Every subset of the empty set is the empty set.                          *)
    apply Single.Charac. apply Empty.WhenIncl. apply Charac. assumption.
  - (* Conversely, the empty set is a subset of itself.                         *)
    apply Single.Charac in H1. subst. apply IsIn.
Qed.
