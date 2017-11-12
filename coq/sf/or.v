Require Import nat.

Example or_exercise1 : forall (n m:nat),
    n = 0 \/ m = 0 -> n * m = 0.
Proof.
    intros n m [H1|H2].
    - rewrite H1. reflexivity.
    - rewrite H2. symmetry. apply mult_n_O. 
Qed.


Lemma or_introl : forall (P Q:Prop),
    P -> P \/ Q.
Proof. intros P Q H. left. exact H. Qed.

Lemma or_intror : forall (P Q:Prop),
    Q -> P \/ Q.
Proof. intros P Q H. right. exact H. Qed.


Lemma zero_or_succ : forall (n:nat),
    n = 0 \/ n = S (pred n).
Proof.
    intros n. destruct n as [|n].
    - left. reflexivity.
    - right. reflexivity.
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

Lemma or_comm : forall (P Q:Prop),
    P \/ Q -> Q \/ P.
Proof.
    intros P Q [H1|H2].
    - right. exact H1.
    - left. exact H2.
Qed.




