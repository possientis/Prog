Require Import Coq.Arith.PeanoNat.

Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Subst.
Require Import ZF.Meta.Syntax.

Definition Unique (A:Term) : Term :=
  All
    (All
      (Imp
        (App (shiftT 2 A) (Var 1))
        (Imp
          (App (shiftT 2 A) (Var 0))
          (Equal (Var 1) (Var 0))))).

(* Lifting commutes with unique class membership.                               *)
Proposition ShiftT : forall (A:Term) (i j:nat),
  Shift.fromT i j (Unique A) = Unique (Shift.fromT i j A).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros A i j. unfold Unique, shiftT. simpl.
  assert (i + 2 = S (S i)) as H1. {
    rewrite Nat.add_succ_r. rewrite Nat.add_1_r. reflexivity. }
  rewrite <- H1, CommT. 2: apply Nat.le_0_l. reflexivity.
Qed.

(* Substitution commutes with unique class membership.                          *)
Proposition SubstT : forall (A:Term) (i:nat) (r:nat -> Term),
  Subst.fromT i r (Unique A) = Unique (Subst.fromT i r A).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros A i r. unfold Unique, shiftT. simpl.
  assert (S (S i) = 0 + 2 + i) as H1. { reflexivity. }
  rewrite H1. rewrite SubstShiftT. reflexivity.
Qed.
