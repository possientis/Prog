Inductive isZero : nat -> Prop :=
| IsZero : isZero 0
.

Lemma isZero_0 : isZero 0.
Proof. constructor. Qed.

Lemma isZero_plus : forall (n m:nat), isZero m -> n + m = n.
Proof.
    intros n m H. destruct H. rewrite <- plus_n_O. reflexivity.
Qed.


Lemma not_isZero_1 : ~ isZero 1.
Proof.
    intros H. remember 1 as n eqn:E. revert E. destruct H.
    intros. discriminate.
Qed.


Lemma not_isZero_1' : ~ isZero 1.
Proof. intros H. inversion H. Qed.

Inductive even : nat -> Prop :=
| EvenO  : even 0
| EvenSS : forall (n:nat), even n -> even (S (S n))
.

Lemma even_0 : even 0.
Proof. constructor. Qed.

Lemma even_4 : even 4.
Proof. constructor. constructor. constructor. Qed.

(* Hint Constructors even. *)

Lemma even_4' : even 4.
Proof. constructor. constructor. constructor. Qed.

Lemma even_1_contra : ~ even 1.
Proof. intros H. inversion H. Qed.

Lemma even_3_contra : ~ even 3.
Proof. intros H. inversion H as [H0|n H2 H3]. inversion H2. Qed.


Lemma even_plus : forall (n m:nat), even n -> even m -> even (n + m).
Proof.
    intros n m Hn. revert m. induction Hn as [|n H IH].
    - auto.
    - intros m Hm. simpl. rewrite plus_n_Sm, plus_n_Sm.
      apply IH. constructor. assumption.
Qed.

Lemma even_twice : forall (n:nat), even (n + n).
Proof.
    induction n as [|n IH]; simpl.
    - constructor.
    - rewrite <- plus_n_Sm. constructor. assumption.
Qed.

Lemma even_back : forall (n:nat), even (S (S n)) -> even n.
Proof.
    intros n H. remember (S (S n)) as m eqn:E in H.
    revert E. revert n. destruct H as [|n H].
    - intros n H. inversion H.
    - intros m H'. inversion H'. subst. assumption.
Qed.


Lemma even_succ_contra : forall (n:nat), even n -> ~ even (S n).
Proof.
    intros n. induction n as [|n IH].
    - intros H1 H2. inversion H2.
    - intros H1 H2. apply even_back in H2. apply IH; assumption.
Qed.



Lemma even_contra : forall (n:nat), ~ even (S (n + n)).
Proof.
    intros n. apply even_succ_contra, even_twice.
Qed.

