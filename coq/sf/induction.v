Require Import nat.
Require Import bool.
Require Import binary.


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

Theorem plus_assoc : forall n m p:nat, (n + m) + p = n + (m + p).
Proof.
    induction n as [|n H].
    - reflexivity.
    - intros m p. simpl. rewrite H. reflexivity.
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


Theorem mult_0_plus_n : forall n m:nat, (0 + n) * m = n * m.
Proof.
    reflexivity.
Qed.

Theorem mult_n_plus_0 : forall n m:nat, (n + 0) * m = n * m.
Proof.
    intros n m. assert (H: n + 0 = n). (* assert (n + 0 = n) as H *)
    - clear m. induction n. 
        + reflexivity.
        + simpl. rewrite IHn. reflexivity.
    - rewrite H. reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q:nat, 
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
    intros n m p q. assert (n + m = m + n) as H.
    - apply plus_comm.
    - rewrite H. reflexivity.
Qed.


Theorem plus_swap : forall n m p:nat,
    n + (m + p) = m + (n + p).
Proof.
    intros n m p. assert (n + (m + p) = (n + m) + p) as H.
    - rewrite plus_assoc. reflexivity.
    - assert (m + (n + p) = (m + n) + p) as H'.
    + rewrite plus_assoc. reflexivity.
    + rewrite H, H'.  assert (n + m = m + n) as H''. 
    { apply plus_comm. }
    { rewrite H''. reflexivity. }
Qed.

Theorem mult_distrib_left : forall n m p:nat,
    n * (m + p) = n * m + n * p.
Proof.
    induction n as [|n H].
    - reflexivity.
    - intros m p. simpl. rewrite H. clear H.
        assert (m + p + (n * m + n * p) = m + (p + (n * m + n * p))) as H.
        { rewrite plus_assoc. reflexivity. }
        rewrite H. clear H.
        assert (p + (n * m + n * p) = (p + n * m) + n * p) as H.
        { rewrite plus_assoc. reflexivity. }
        rewrite H. clear H.
        assert (m + n * m + (p + n * p) = m + (n * m + (p + n * p))) as H.
        { apply plus_assoc. }
        rewrite H. clear H.
        assert (n * m + (p + n * p) = (n * m + p) + n * p) as H.
        { rewrite plus_assoc. reflexivity. }
        rewrite H. clear H.
        assert (p + n * m = n * m + p) as H.
        { apply plus_comm. }
        rewrite H. clear H. reflexivity.
Qed.

Theorem mult_n_1 : forall n:nat, n * 1 = n.
Proof.
    induction n as [|n H].
    - reflexivity.
    - simpl. rewrite H. reflexivity.
Qed.

Theorem plus_1_n : forall n:nat, 1 + n = S n.
Proof.
    reflexivity.
Qed.

Theorem mult_comm : forall n m: nat, n * m = m * n.
Proof.
    induction n as [|n H].
    - intros m. simpl. rewrite mult_n_0. reflexivity. 
    - intros m. simpl. rewrite H. clear H.
    assert (m + m * n = m * 1 + m * n) as H.
    { rewrite mult_n_1. reflexivity. }
    rewrite H. clear H. 
    rewrite <- mult_distrib_left. rewrite plus_1_n. reflexivity.
Qed.

Theorem leb_refl : forall n:nat, leb n n = true.
Proof.
    induction n as [|n H].
    - reflexivity.
    - simpl. exact H.
Qed.

Theorem zero_neqb_S : forall n:nat, eqb 0 (S n) = false.
Proof.
    reflexivity.
Qed.


Theorem andb_false_r : forall b:bool, andb b false = false.
Proof.
    destruct b.
    - reflexivity.
    - reflexivity.
Qed.

Theorem plus_leb_compat_left : forall n m p:nat, 
    leb n m = true -> leb (p + n) (p + m) = true.
Proof.
    induction p as [|p H].
    - simpl. intro H. exact H.
    - intros H'. simpl. apply H. exact H'.
Qed.

Theorem S_neqb_0: forall n:nat, eqb (S n) 0 = false.
Proof.
    reflexivity.
Qed.

Theorem mult_1_n : forall n:nat, 1 * n = n.
Proof.
    intros n. simpl. rewrite plus_n_0. reflexivity.
Qed.


Theorem all3_spec: forall a b:bool,
    orb (andb a b) (orb (negb a) (negb b)) = true.
Proof.
    destruct a, b.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
Qed.

Theorem mult_distrib_right : forall n m p:nat,
    (n + m) * p = n * p + m * p.
Proof.
    intros n m p. 
    assert ((n + m) * p = p * (n + m)) as H1. { apply mult_comm. }
    assert (n * p = p * n) as H2. {apply mult_comm. }
    assert (m * p = p * m) as H3. {apply mult_comm. }
    rewrite H1, H2, H3. apply mult_distrib_left.
Qed.

Theorem mult_assoc : forall n m p:nat, (n * m) * p = n * (m * p).
Proof.
    induction n as [|n H].
    - reflexivity.
    - intros m p. simpl. rewrite <- H. apply mult_distrib_right.
Qed.

Theorem eqb_refl : forall n:nat, eqb n n = true.
Proof.
    induction n as [| n H].
    - reflexivity.
    - simpl. exact H.
Qed.


Theorem plus_swap' : forall n m p:nat,
    n + (m + p) = m + (n + p).
Proof.
    intros n m p. 
    replace (n + (m + p)) with ((n + m) + p).
    replace (m + (n + p)) with ((m + n) + p).
    replace (m + n) with (n + m).
    reflexivity.
    - apply plus_comm.
    - apply plus_assoc.
    - apply plus_assoc.
Qed.



Theorem double_injective : forall (n m:nat),
    double n = double m -> n = m.
Proof.
    induction n as [|n H].
    - intros m H. destruct m as [|m].
        + reflexivity.
        + simpl in H. inversion H.
    - intros m H'. destruct m as [|m].
        + simpl in H'. inversion H'.
        + simpl in H'. inversion H' as [H1]. clear H'.
            apply H in H1. rewrite H1. reflexivity.
Qed.

Theorem double_induction : forall (P: nat -> nat -> Prop),
    P 0 0 ->
    (forall m, P m 0 -> P (S m) 0) ->
    (forall n, P 0 n -> P 0 (S n)) ->
    (forall m n, P m n -> P (S m) (S n)) ->
    forall m n, P m n.
Proof.
    intros P H0 H1 H2 H3. induction m as [| m H].
    - induction n as [| n H].
        + exact H0.
        + apply H2. exact H.
    - destruct n.
        + assert (forall q, P q 0).
            { induction q as [|q H'].
                - exact H0.
                - apply H1. exact H'.
            } 
            apply H4.
        + apply H3. apply H.
Qed.
            

Lemma plus_comm3 : forall (n m p:nat),
    n + (m + p) = (p + m) + n.
Proof.
    intros n m p.
    rewrite plus_comm.
    assert (H : m + p = p + m). { rewrite plus_comm. reflexivity. }
    rewrite H. reflexivity.
Qed.
    

Lemma plus_comm3' : forall (n m p:nat),
    n + (m + p) = (p + m) + n.
Proof.
    intros n m p. rewrite plus_comm. rewrite (plus_comm m). reflexivity.
Qed.

Theorem evenb_double : forall (k:nat), evenb (double k) = true.
Proof.
    induction k as [|k H].
    - reflexivity.
    - simpl. exact H.
Qed.

