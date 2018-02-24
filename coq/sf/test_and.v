Example and_exercise1 : forall (n m:nat), 
    n + m = 0 -> n = 0 /\ m = 0.
Proof.
    intros n m H. destruct n, m.
    - split.
        + reflexivity.
        + reflexivity.
    - inversion H.
    - inversion H.
    - inversion H.
Qed.

Example and_exercise2 : forall (n m:nat),
    n = 0 /\ m = 0 -> n + m = 0.
Proof.
    intros n m H. destruct H as [H1 H2].
    rewrite H1, H2. reflexivity.
Qed.

Example and_exercise3 : forall (n m:nat),
    n = 0 /\ m = 0 -> n + m = 0.
Proof.
    intros n m [H1 H2]. rewrite H1,H2. reflexivity.
Qed.


Example and_exercise4 : forall (n m:nat),
    n + m = 0 -> n * m = 0.
Proof.
    intros n m H. assert (H': n = 0 /\ m = 0).
    { apply and_exercise1. exact H. }
    destruct H' as [H1 H2]. rewrite H1. reflexivity.
Qed.


Lemma proj1 : forall (P Q: Prop),
    P /\ Q -> P.
Proof. intros P Q [H1 H2]. exact H1. Qed.

Lemma proj2 : forall (P Q: Prop),
    P /\ Q -> Q.
Proof. intros P Q [H1 H2]. exact H2. Qed.


Definition and_comm_aux (P Q:Prop) (H:P /\ Q) : Q /\ P :=
    match H with
    | conj p q   => conj q p
    end.

Definition and_comm' (P Q:Prop) : P /\ Q <-> Q /\ P :=
    conj (and_comm_aux P Q) (and_comm_aux Q P).

Definition conj_fact : forall (P Q R:Prop), P /\ Q -> Q /\ R -> P /\ R :=
    fun (P Q R:Prop) =>
        fun (pq : P /\ Q) =>
            fun (qr : Q /\ R) =>
                match pq, qr with
                | conj p _, conj _ r => conj p r
                end . 



