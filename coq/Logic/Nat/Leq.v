Require Import Le.

Require Import Logic.Nat.Eq.

Lemma not_le_Sn_n : forall (n:nat), ~ S n <= n.
Proof.
    induction n as [|n IH]; intros H.
    - inversion H.
    - apply IH. apply le_S_n. assumption.
Qed.

Lemma le_0 : forall (n:nat), n <= 0 -> n = 0.
Proof.
    intros [|n].
    - intros _.  reflexivity.
    - intros H. inversion H. 
Qed.

Lemma le_0_n : forall (n:nat), 0 <= n.
Proof.
    induction n as [|n IH].
    - apply le_n.
    - apply le_S. assumption.
Qed.

