Require Import bool.


Inductive nat : Type :=
    | O : nat
    | S : nat -> nat
    .

Notation "0" := (O).
Notation "1" := (S 0).
Notation "2" := (S 1).
Notation "3" := (S 2).
Notation "4" := (S 3).
Notation "5" := (S 4).
Notation "6" := (S 5).
Notation "7" := (S 6).
Notation "8" := (S 7).
Notation "9" := (S 8).
Notation "10" := (S 9).
Notation "11" := (S 10).
Notation "12" := (S 11).
Notation "13" := (S 12).
Notation "14" := (S 13).
Notation "15" := (S 14).
Notation "16" := (S 15).
Notation "17" := (S 16).
Notation "18" := (S 17).
Notation "19" := (S 18).
Notation "20" := (S 19).
Notation "21" := (S 20).
Notation "22" := (S 21).
Notation "23" := (S 22).
Notation "24" := (S 23).
Notation "25" := (S 24).

Definition pred (n:nat) : nat :=
    match n with    
        | O     => O
        | S p   => p
    end.

Fixpoint evenb (n:nat) : bool :=
    match n with 
        | O         => true
        | S O       => false
        | S (S p)   => evenb p
    end.

Definition oddb (n:nat) : bool := negb (evenb n).

Fixpoint plus (n:nat)(m:nat) : nat :=
    match n with 
        | O     => m
        | S p   => S (plus p m)
    end.

Fixpoint mult (n m:nat) : nat :=
    match n with 
        | O     => O
        | S p   => plus m (mult p m)
    end.

Fixpoint minus (n m:nat) : nat :=
    match n,m with
        | O   , _   => O
        | S _ , O   => n
        | S p , S q => minus p q
    end.

Fixpoint exp (base power : nat) : nat :=
    match power with
        | O     => S O
        | S p   => mult base (exp base p)
    end.


Fixpoint fact (n:nat) : nat :=
    match n with
        | O     => 1
        | S p   => mult n (fact p)
    end.


Notation "x + y" := (plus x y) (at level 50, left associativity).

Notation "x - y" := (minus x y) (at level 50, left associativity).  

Notation "x * y" := (mult x y) (at level 40, left associativity).

Fixpoint eqb (n m:nat) : bool := 
    match n with
        | O     =>  match m with
                        | O     => true
                        | S _   => false
                    end
        | S p   =>  match m with
                        | O     => false
                        | S q   => eqb p q
                    end
    end.

Fixpoint leb (n m:nat) : bool :=
    match n with
        | O     =>  true
        | S p   =>  match m with
                        | O     => false
                        | S q   => leb p q
                    end
    end.

Definition ltb (n m:nat) : bool :=
    andb (leb n m) (negb (eqb n m)).    

Lemma plus_0_n : forall n:nat, 0 + n = n.
Proof.
    intros n. simpl. reflexivity.
Qed.

Lemma plus_1_n : forall n:nat, 1 + n = S n.
Proof.
    intros n. reflexivity.
Qed.

Lemma mult_0_n : forall n:nat, 0 * n = 0.
Proof.
    intros n. reflexivity.
Qed.

Lemma plus_n_0 : forall n:nat, n + 0 = n.
Proof.
    intros n. elim n.
    clear n. reflexivity.
    clear n. intros n H. simpl. rewrite H. reflexivity.
Qed.

Lemma mult_n_0 :forall (n:nat), n * 0 = 0.
Proof.
    intros n. induction n as [|n IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.

Lemma mult_1_n : forall n:nat, 1 * n = n.
Proof.
    intros n. simpl. apply plus_n_0.
Qed.

Lemma mult_0_plus : forall n m:nat,
    (0 + n) * m = n * m.
Proof.
    intros n m. rewrite plus_0_n. reflexivity.
Qed.

Lemma  mult_S_1 : forall n m:nat,
    m = S n -> m * (1 + n) = m * m.
Proof.
    intros n m H. simpl. rewrite <- H. reflexivity.
Qed.

Lemma plus_1_neq_0 : forall n:nat,
    eqb (n + 1) 0 = false.
Proof.
    intros n. elim n.
    clear n. simpl. reflexivity.
    clear n. intros n H. simpl. reflexivity.
Qed.

Lemma zero_nbeq_plus_1 : forall n:nat,
    eqb 0 (n + 1) = false.
Proof.
    intros [|n].
    - reflexivity.
    - reflexivity.
Qed.

Lemma plus_n_Sm : forall n m:nat, n + S m = S (n + m).
Proof.
    induction n.
    - reflexivity. 
    - intros m. simpl. rewrite IHn. reflexivity. 
Qed.


Lemma plus_Sn_m: forall n m:nat, S n + m = S (n + m).
Proof. intros n m. reflexivity. Qed.

Theorem plus_comm : forall n m:nat, n + m = m + n.
Proof.
    induction n as [|n IH]. 
    - intros m. symmetry. apply plus_n_0.
    - intros m. rewrite plus_n_Sm. simpl. rewrite IH. reflexivity.
Qed.

Theorem plus_assoc : forall n m p:nat, (n + m) + p = n + (m + p).
Proof.
    induction n as [|n H].
    - reflexivity.
    - intros m p. simpl. rewrite H. reflexivity.
Qed.


Lemma eqb_refl : forall n:nat, eqb n n = true.
Proof.
    induction n as [|n H].
    - reflexivity.
    - simpl. exact H.
Qed.


Lemma true_not_false : true <> false.
Proof.
    intro H. discriminate H.
Qed.

Theorem eqb_semantics : forall n m:nat,
    n = m <-> eqb n m = true.
Proof.
 intros n m. split.
 - intros H. rewrite H. apply eqb_refl.
 - generalize m. clear m. induction n as [|n H]. 
    + destruct m.
        { intros H. reflexivity. }
        { simpl. intros H. discriminate H. }
    + destruct m.
        { simpl. intros H'. discriminate H'. }
        { simpl. intros H'. 
          assert (n = m) as H''. { apply H. exact H'. }
          rewrite H''. reflexivity. }
Qed.


Theorem eqb_semantics' : forall (n m: nat),
    n = m <-> eqb n m = true.
Proof.
    split.
    - intros H. rewrite H. apply eqb_refl. 
    - generalize m. clear m. induction n as [| n H].
        + destruct m. 
            { intros. reflexivity. }
            { simpl. intros H. inversion H. }
        + destruct m.
            { simpl. intros H'. inversion H'. }
            { simpl. intros H'. apply H in H'. rewrite H'. reflexivity. }
Qed.
        

Theorem eqb_sym : forall (n m:nat),
    eqb n m = eqb m n.
Proof.
    induction n as [|n H].
    - destruct m. 
        + reflexivity.
        + reflexivity.
    - destruct m.
        + reflexivity. 
        + apply H.
Qed.

Theorem eqb_trans : forall (n m p:nat),
    eqb n m = true -> eqb m p = true -> eqb n p = true.
Proof.
   intros n m p Hnm Hmp. 
   apply eqb_semantics. 
   apply eqb_semantics in Hnm.
   apply eqb_semantics in Hmp.
   apply eq_trans with (y:=m).
   exact Hnm.
   exact Hmp.
Qed.

Theorem eqb_false_iff : forall (n m:nat),
    eqb n m = false <-> n <> m.
Proof.
    intros n m. split.
    - intros H H'. rewrite H' in H. rewrite eqb_refl in H. inversion H.
    - intros H. destruct (eqb n m) eqn: Enm. 
        + apply eqb_semantics in Enm. exfalso. apply H. exact Enm.
        + reflexivity.
Qed.

Lemma not_n_Sn : forall (n:nat), n <> S n.
Proof.
  intros n. induction n as [|n IH].
  - intros H. inversion H.
  - intros H. inversion H as [H']. apply IH. exact H'.
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

Lemma mult_eq_0 : forall (n m:nat),
    n * m = 0 -> n = 0 \/ m = 0.
Proof.
    intros n m H. destruct n, m.
    - left. reflexivity.
    - left. reflexivity.
    - right. reflexivity.
    - inversion H.
Qed.


Example or_0_0_mult_0 : forall (n m:nat),
    n = 0 \/ m = 0 -> n * m = 0.
Proof.
    intros n m [H1|H2].
    - rewrite H1. reflexivity.
    - rewrite H2. apply mult_n_0. 
Qed.

Lemma mult_0 : forall (n m:nat),
    n * m = 0 <-> n = 0 \/ m = 0.
Proof.
    split. 
    - apply mult_eq_0.
    - apply or_0_0_mult_0.
Qed.

Lemma zero_or_succ : forall (n:nat),
    n = 0 \/ n = S (pred n).
Proof.
    intros n. destruct n as [|n].
    - left. reflexivity.
    - right. reflexivity.
Qed.





