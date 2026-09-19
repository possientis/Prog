Require Import Coq.Arith.PeanoNat.

Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Subst.
Require Import ZF.Meta.Syntax.

Definition Small (A:Term) : Term :=
  Ex
    (All
      (Iff
        (Elem (Var 0) (Var 1))
        (App (shiftT 2 A) (Var 0)))).

(* Lifting commutes with small class witnesses.                                 *)
Proposition ShiftT : forall (A:Term) (i j:nat),
  Shift.fromT i j (Small A) = Small (Shift.fromT i j A).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros A i j. unfold Small, shiftT. simpl.
  assert (i + 2 = S (S i)) as H1. {
    rewrite Nat.add_succ_r. rewrite Nat.add_1_r. reflexivity. }
  rewrite <- H1, CommT. 2: apply Nat.le_0_l. reflexivity.
Qed.

(* Substitution commutes with small class witnesses.                            *)
Proposition SubstT : forall (A:Term) (i:nat) (r:nat -> Term),
  Subst.fromT i r (Small A) = Small (Subst.fromT i r A).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros A i r. unfold Small, shiftT. simpl.
  assert (S (S i) = 0 + 2 + i) as H1. { reflexivity. }
  rewrite H1. rewrite SubstShiftT. reflexivity.
Qed.
