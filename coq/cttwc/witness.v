Inductive Sig (a:Type) (p:a -> Type) : Type :=
| Ex : forall (x:a), p x -> Sig a p
.

Arguments Sig {a}.
Arguments Ex {a} {p}.


(* Elim restriction, cant do the obvious.                                       *)
Definition witness : forall (f:nat -> bool),
    (exists (n:nat), f n = true) -> Sig (fun n => f n = true).
Proof.
Admitted.


Definition Guarded (f:nat -> bool) (n:nat) : Prop :=
    exists (k:nat), f (n + k) = true.

Lemma L1 : forall (f:nat -> bool) (n:nat), f n = true -> Guarded f n.
Proof.
    intros f n H. exists 0. rewrite <- plus_n_O. assumption.
Qed.

Lemma L2 : forall (f:nat -> bool) (n:nat), Guarded f (S n) -> Guarded f n.
Proof.
    intros f n [k H1]. exists (S k). rewrite <- plus_n_Sm. assumption.
Qed.

Lemma L3 : forall (f:nat -> bool), (exists (k:nat), f k = true) -> Guarded f 0.
Proof.
    intros f [k H1]. exists k. assumption.
Qed.

Lemma L4 : forall (f:nat -> bool) (n:nat), 
    Guarded f n -> f n = false -> Guarded f (S n).
Proof.
    intros f n [k H1] H2. destruct k as [|k].
    - rewrite <- plus_n_O in H1. rewrite H1 in H2. inversion H2.
    - exists k. rewrite <- plus_n_Sm in H1. assumption.
Qed.


Inductive G (f:nat -> bool) : nat -> Prop :=
| mkG : forall (n:nat), (f n = false -> G f (S n)) -> G f n
.

Lemma L5 : forall (f:nat -> bool) (n:nat), f n = true -> G f n.
Proof.
    intros f n H1. constructor. intros H2. rewrite H1 in H2. inversion H2.
Qed.

Lemma L6 : forall (f:nat -> bool) (n:nat), G f (S n) -> G f n.
Proof.
    intros f n H1. constructor. intros H2. assumption.    
Qed.

Lemma L7 : forall (f:nat -> bool) (n:nat), G f n -> G f 0.
Proof.
    intros f. induction n as [|n IH].
    - auto.
    - intros H1. apply IH. apply L6. assumption.
Qed.

Lemma L8 : forall (f:nat -> bool), (exists (n:nat), f n = true) -> G f 0.
Proof.
    intros f [n H1].  apply L7 with n. apply L5. assumption.
Qed.

Definition L9 : forall (f:nat -> bool) (n:nat), G f n -> Sig (fun k => f k = true).
Proof.
    intros f n H1.
Show.

