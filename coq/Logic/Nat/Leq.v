Require Import Le.

Require Import Logic.Nat.Eq.

Lemma not_le_Sn_n : forall (n:nat), ~ S n <= n.
Proof.
    induction n as [|n IH]; intros H.
    - inversion H.
    - apply IH. apply le_S_n. assumption.
Defined.

Lemma le_0 : forall (n:nat), n <= 0 -> n = 0.
Proof.
    intros [|n].
    - intros _.  reflexivity.
    - intros H. inversion H. 
Defined.

Lemma le_0_n : forall (n:nat), 0 <= n.
Proof.
    induction n as [|n IH].
    - apply le_n.
    - apply le_S. assumption.
Defined.

Lemma not_le_ge : forall (n m:nat), ~ n <= m -> S m <= n.
Proof.
    intros n m. revert m n. induction m as [|m IH]; intros n H1.
    - destruct n as [|n].
        + exfalso.  apply H1, le_n.
        + apply le_n_S, le_0_n.
    - destruct n as [|n].
        + exfalso. apply H1, le_0_n. 
        + apply le_n_S, IH. intros H2. apply H1. apply le_n_S. assumption.
Defined.

