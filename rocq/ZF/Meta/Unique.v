Require Import Coq.Arith.PeanoNat.

Require Import ZF.Meta.Shift.
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
Proposition FromT : forall (A:Term) (i j:nat),
  fromT i j (Unique A) = Unique (fromT i j A).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros A i j. unfold Unique, shiftT. simpl.
  assert (i + 2 = S (S i)) as H1. {
    rewrite Nat.add_succ_r. rewrite Nat.add_1_r. reflexivity. }
  rewrite <- H1, CommT. 2: apply Nat.le_0_l. reflexivity.
Qed.
