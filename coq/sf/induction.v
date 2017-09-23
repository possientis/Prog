
Theorem plus_n_0 : forall n:nat, n = n + 0.
Proof.
    intros n. elim n.
    - clear n. simpl. reflexivity.
    - clear n. intros n H. simpl. rewrite <- H. reflexivity.
Qed.

Theorem plus_n_0' : forall n:nat, n = n + 0.
Proof.
    intros n. induction n as [|n H].
    - simpl. reflexivity.
    - simpl. rewrite <- H. reflexivity. 
Qed.

Theorem minus_diag : forall n:nat, n - n = 0.
Proof.
    intros n. induction n.
    - simpl. reflexivity.
    - simpl. rewrite IHn. reflexivity.
Qed.

Theorem minus_diagi' : forall n:nat, n - n = 0. 
Proof.
    induction n.
    - simpl. reflexivity.
    - simpl. rewrite IHn. reflexivity.
Qed. 

Theorem mult_0_n : forall n:nat, 0 * n = 0.
Proof.
    reflexivity.
Qed.

Theorem mult_n_0 : forall n:nat, n * 0 = 0.
Proof.
    induction n.
    - reflexivity.
    - exact IHn.
Qed.

Theorem plus_n_Sm : forall n m:nat, n + S m = S (n + m).
Proof.
    induction n.
    - reflexivity. 
    - intros m. simpl. rewrite IHn. reflexivity. 
Qed.

Theorem plus_comm : forall n m:nat, n + m = m + n.
Proof.
    induction n. 
    - apply plus_n_0.
    - intros m. simpl. rewrite plus_n_Sm. rewrite IHn. reflexivity.
Qed.

Theorem plus_assoc : forall n m p:nat, n + (m + p) = (n + m) + p.
Proof.
    induction n.
    - reflexivity.
    - intros m p. simpl. rewrite IHn. reflexivity.
Qed.

Fixpoint double (n:nat) : nat :=
    match n with
        | O     => O
        | S p   => S (S (double p))
    end.

Lemma double_plus : forall n:nat, double n = n + n.
Proof.
    induction n.
    - reflexivity.
    - simpl. rewrite plus_n_Sm. rewrite IHn. reflexivity. 
Qed.

Fixpoint evenb (n:nat) : bool :=
    match n with 
        | O         => true
        | S O       => false
        | S (S p)   => evenb p
    end.

Lemma negb_negb : forall b:bool, negb (negb b) = b.
Proof.
    destruct b.
    - reflexivity.
    - reflexivity.
Qed.

Theorem evenb_S : forall n:nat, evenb (S n) = negb (evenb n).
Proof.
    induction n.
    - reflexivity.
    - rewrite IHn. simpl. rewrite negb_negb. reflexivity.
Qed.






