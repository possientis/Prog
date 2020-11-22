Require Import Peano_dec.

Require Import Logic.Class.Eq.

Lemma not_eq_s_n : forall (n:nat), ~ S n = n.
Proof.
    induction n as [|n IH]; intros H.
    - inversion H.
    - injection H. intros H'. apply IH. assumption.
Defined.

(* TODO: issue already has an Eq instance from Ord                              *)
Instance EqNat : Eq nat := { eqDec := eq_nat_dec }.


