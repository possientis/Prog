Require Import Coq.Arith.PeanoNat.

Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Syntax.

Definition Exists (A:Term) : Term := Ex (App (shiftT 1 A) (Var 0)).

(* Lifting commutes with existential class membership.                          *)
Proposition FromT : forall (A:Term) (i j:nat),
  fromT i j (Exists A) = Exists (fromT i j A).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros A i j. unfold Exists, shiftT. simpl.
  assert (i + 1 = S i) as H1. { rewrite Nat.add_1_r. reflexivity. }
  rewrite <- H1, CommT. 2: apply Nat.le_0_l. reflexivity.
Qed.

