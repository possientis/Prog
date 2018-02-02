Require Import nat.
Require Import bool.


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

Fixpoint double (n:nat) : nat :=
    match n with
        | O     => O
        | S p   => S (S (double p))
    end.

Lemma double_plus : forall n:nat, double n = n + n.
Proof.
    induction n as [|n IH].
    - reflexivity.
    - simpl. rewrite plus_n_Sm. rewrite IH. reflexivity.
Qed.


Theorem evenb_S : forall n:nat, evenb (S n) = negb (evenb n).
Proof.
    induction n.
    - reflexivity.
    - rewrite IHn. simpl. rewrite negb_involutive. reflexivity.
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

Lemma evenb_negb_gen : forall (n:nat),
(forall b:bool, evenb n = b -> evenb (S n) = negb b) /\
(forall b:bool, evenb (S n) = b -> evenb n = negb b).
Proof.
    induction n as [|n [H1 H2]].
    - split. 
        + intros b H'. rewrite <- H'. reflexivity.
        + intros b H'. rewrite <- H'. reflexivity.
    - split.
        + intros b H'. apply H2. exact H'.
        + intros b H'. apply H1. exact H'.
Qed.


Lemma evenb_negb : forall (n:nat) (b:bool),
    evenb n = b -> evenb (S n) = negb b.
Proof.
    intros n b. assert (
    (forall b:bool, evenb n = b -> evenb (S n) = negb b) /\
    (forall b:bool, evenb (S n) = b -> evenb n = negb b) ) as [H1 H2]. 
        { apply evenb_negb_gen. }
    apply H1.
Qed.


Theorem evenb_double_conv : forall (n:nat), 
    exists k, n = if evenb n 
        then double k
        else S (double k).
Proof.
    induction n as [|n H].
    - exists 0. reflexivity.
    - destruct (evenb n) eqn: H'. 
        + destruct H as [k H]. exists k. 
            apply evenb_negb in H'. rewrite H'. rewrite H. reflexivity.
        + destruct H as [k H]. exists (S k).
            apply evenb_negb in H'. rewrite H'. simpl. rewrite H. reflexivity.
Qed.

Theorem even_bool_prop : forall (n:nat),
    evenb n = true <-> exists k, n = double k.
Proof.
    intros n. split.
    - intros H. assert ( exists k, n = if evenb n 
        then double k
        else S (double k) ) as [k H']. { apply evenb_double_conv. }
            rewrite H in H'. exists k. exact H'.
    - intros [k H]. rewrite H. apply evenb_double.
Qed.

