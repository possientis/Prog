Require Import Le.
Require Import Plus.

Lemma le_0 : forall (n:nat), n <= 0 -> n = 0.
Proof.
    intros [|n].
    - intros _.  reflexivity.
    - intros H. inversion H. 
Qed.

Lemma sum_0 : forall (n m:nat), n + m = 0 -> n = 0 /\ m = 0.
Proof.
    intros [|n] [|m].
    - intros _. split; reflexivity.
    - intros H. inversion H.
    - intros H. inversion H.
    - intros H. inversion H.
Qed.

Lemma n_le_max : forall (n m:nat), n <= max n m.
Proof.
    induction n as [|n IH].
        - induction m as [|m IH'].
            + apply le_n.
            + apply le_S. assumption.
        - induction m as [|m IH'].
            + apply le_n.
            + apply le_n_S, IH.
Qed.

Lemma max_sym : forall (n m:nat), max n m = max m n.
Proof.
    induction n as [|n IH].
        - induction m as [|m IH']; reflexivity.
        - induction m as [|m IH'].
            + reflexivity.
            + simpl. rewrite IH. reflexivity.
Qed.

Lemma m_le_max : forall (n m:nat), m <= max n m.
Proof.
    intros n m. rewrite max_sym. apply n_le_max.
Qed.

Lemma weaken_r : forall (x y z n:nat),
    (x + z <= n) -> (y <= z) -> x + y <= n.
Proof.
    intros x y z n H1 H2.
    apply le_trans with (x + z).
    - apply plus_le_compat_l. assumption.
    - assumption.
Qed.

Lemma weaken_l : forall (x y z n:nat),
    (z + y <= n) -> (x <= z) -> x + y <= n.
Proof.
    intros x y z n H1 H2.
    apply le_trans with (z + y).
    - apply plus_le_compat_r. assumption.
    - assumption.
Qed.

Lemma weaken_l' : forall (x y z n:nat),
    (z + y <= S n) -> (S x <= z) -> x + y <= n.
Proof.
    intros x y z n H1 H2. apply le_S_n.
    apply le_trans with (z + y). 
    - apply (plus_le_compat_r (S x) z y). assumption.
    - assumption.
Qed.

