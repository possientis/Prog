Require Import Le.
Require Import Plus.
Require Import List.
Require Import Compare_dec.

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

Lemma not_eq_s_n : forall (n:nat), ~ S n = n.
Proof.
    induction n as [|n IH]; intros H.
    - inversion H.
    - injection H. intros H'. apply IH. assumption.
Qed.

Lemma not_le_s_n : forall (n:nat), ~ S n <= n.
Proof.
    intros n H. apply (not_eq_s_n n). apply le_antisym.
    - assumption.
    - apply le_S, le_n.
Qed.

Lemma sum_0 : forall (n m:nat), n + m = 0 -> n = 0 /\ m = 0.
Proof.
    intros [|n] [|m].
    - intros _. split; reflexivity.
    - intros H. inversion H.
    - intros H. inversion H.
    - intros H. inversion H.
Qed.

Lemma max_n_0 : forall (n:nat), max n 0 = n.
Proof.
    destruct n as [|n]; reflexivity.
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

Lemma max_lub : forall (n m N:nat), n <= N -> m <= N -> max n m <= N.
Proof.
    intros n m N. revert m N. induction n as [|n IH].
    - simpl. intros. assumption.
    - intros m N H1 H2. simpl. destruct m as [|m].
        + assumption.
        + destruct N as [|N].
            { inversion H1. }
            { apply le_n_S. apply IH; apply le_S_n; assumption. }
Qed.


Lemma weaken_r : forall (x y y' n:nat),
    (x + y' <= n) -> (y <= y') -> x + y <= n.
Proof.
    intros x y y' n H1 H2.
    apply le_trans with (x + y').
    - apply plus_le_compat_l. assumption.
    - assumption.
Qed.

Lemma weaken_l : forall (x x' y n:nat),
    (x' + y <= n) -> (x <= x') -> x + y <= n.
Proof.
    intros x x' y n H1 H2.
    apply le_trans with (x' + y).
    - apply plus_le_compat_r. assumption.
    - assumption.
Qed.

Lemma weaken_l' : forall (x x' y n:nat),
    (x' + y <= S n) -> (S x <= x') -> x + y <= n.
Proof.
    intros x x' y n H1 H2. apply le_S_n.
    apply le_trans with (x' + y). 
    - apply (plus_le_compat_r (S x) x' y). assumption.
    - assumption.
Qed.

Lemma weaken3_l : forall (x x' y z n:nat),
    (x' + y + z <= n) -> (x <= x') -> x + y + z <= n.
Proof.
    intros x x' y z n H1 H2. apply weaken_l with (x' + y).
    - assumption.
    - apply plus_le_compat_r. assumption.
Qed.

Lemma weaken3_m : forall (x y y' z n:nat),
    (x + y' + z <= n) -> (y <= y') -> x + y + z <= n.
Proof.
    intros x y y' z n H1 H2. apply weaken_l with (x + y').
    - assumption.
    - apply plus_le_compat_l. assumption.
Qed.

Fixpoint maximum (ns:list nat) : nat :=
    match ns with
    | nil       => 0
    | cons n ns => max n (maximum ns)
    end.    

Lemma maximum_lub : forall (ns:list nat) (N:nat), 
    (forall (n:nat), In n ns -> n <= N) -> maximum ns <= N.
Proof.
    intros ns N. induction ns as [|n ns IH].
    - intros _. apply le_0_n.
    - intros H. simpl. apply max_lub.
        + apply H. left. reflexivity.
        + apply IH. intros m Hm. apply H. right. assumption.
Qed.

Lemma maximum_ubound : forall (ns:list nat) (n:nat),
    In n ns -> n <= maximum ns.
Proof.
    induction ns as [|n' ns IH].
    - intros n H. inversion H.
    - intros n [H|H].
        + subst. apply n_le_max.
        + apply le_trans with (maximum ns).
            { apply IH. assumption. }
            { apply m_le_max. }
Qed.


Lemma natMinimal : forall (ns:list nat), ns <> nil ->
    exists (n:nat), In n ns /\ forall (m:nat), In m ns -> n <= m.
Proof.
    induction ns as [|x xs IH].
    - intros H. exfalso. apply H. reflexivity.
    - intros _. destruct xs as [|y ys].
        + exists x. split.
            { left. reflexivity. }
            { intros m [H|H].
                { rewrite H. reflexivity. }
                { inversion H. }}
        + assert (y :: ys <> nil) as P. { intros H. inversion H. }
          destruct (IH P) as [n' [H1 H2]].
          destruct (le_le_S_dec x n') as [H3|H3].
            { exists x. split.
                { left. reflexivity. }
                { intros m [H4|[H4|H4]].
                    { rewrite <- H4. apply le_n. }
                    { rewrite <- H4. apply le_trans with n'.
                        { assumption. }
                        { apply H2. left. reflexivity. }}
                    { apply le_trans with n'.
                        { assumption. }
                        { apply H2. right. assumption. }}}}
            { exists n'. split.
                { right. assumption. }
                { intros m [H4|[H4|H4]].
                    { rewrite <- H4. apply le_trans with (S n').
                        { apply le_S, le_n. }
                        { assumption. }}
                    { apply H2. left. assumption. }
                    { apply H2. right. assumption. }}}
Qed.


Lemma noDecreasingSeq : ~ exists (f:nat -> nat), forall (n:nat), f (S n) < f n.
Proof.
    intros [f H]. 
    assert (forall (n:nat), n + f n <= f 0) as H'.
        { induction n as [|n IH].
            - apply le_n.
            - apply le_trans with (n + f n).
                + simpl. apply plus_lt_compat_l. apply H.
                + apply IH. }
    assert (S (f 0) <= f 0) as C.
        { apply le_trans with (S (f 0) + f (S (f 0))).
            - apply le_plus_l.
            - apply H'. }
    apply not_le_s_n with (f 0). assumption.    
Qed.

