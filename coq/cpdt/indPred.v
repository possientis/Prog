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

Hint Constructors even.

Lemma even_4' : even 4.
Proof. auto. Qed.

Lemma even_1_contra : ~ even 1.
Proof. intros H. inversion H. Qed.

Lemma even_3_contra : ~ even 3.
Proof. intros H. inversion H as [H0|n H2 H3]. inversion H2. Qed.

