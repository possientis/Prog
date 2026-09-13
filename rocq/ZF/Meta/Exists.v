Require Import Coq.Arith.PeanoNat.

Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Subst.
Require Import ZF.Meta.Syntax.

Definition Exists (A:Term) : Term := Ex (App (shiftT 1 A) (Var 0)).

(* Lifting commutes with existential class membership.                          *)
Proposition CommShiftT : forall (A:Term) (i j:nat),
  Shift.fromT i j (Exists A) = Exists (Shift.fromT i j A).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros A i j. unfold Exists, shiftT. simpl.
  assert (i + 1 = S i) as H1. { rewrite Nat.add_1_r. reflexivity. }
  rewrite <- H1, CommT. 2: apply Nat.le_0_l. reflexivity.
Qed.

(* Substitution commutes with existential class membership.                     *)
Proposition CommSubstT : forall (A:Term) (i:nat) (r:nat -> Term),
  Subst.fromT i r (Exists A) = Exists (Subst.fromT i r A).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros A i r. unfold Exists, shiftT. simpl.
  assert (S i = 0 + 1 + i) as H1. { reflexivity. }
  rewrite H1. rewrite (proj1 ShiftFrom). reflexivity.
Qed.

