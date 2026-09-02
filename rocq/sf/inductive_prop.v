Require Import nat.
Require Import bool.
Require Import not.
Require Import induction.

Inductive ev : nat -> Prop :=
    | ev_0  : ev 0
    | ev_SS : forall (n:nat), ev n -> ev (S (S n))
    . 


Theorem evSS_ev : forall (n:nat),
    ev (S (S n)) -> ev n.
Proof. intros n H. inversion H as [|n' H']. exact H'. Qed.


Theorem one_not_even : ¬ ev 1.
Proof. intros H. inversion H. Qed.

Theorem ev_even : forall (n:nat),
    ev n -> exists k, n = double k.
Proof.
    intros n H. induction H as [|n H [k H']].
    - exists 0. reflexivity.
    - exists (S k). simpl. rewrite <- H'. reflexivity.
Qed.

Theorem ev_double : forall n, ev (double n).
Proof.
    induction n as [|n H].
    - exact ev_0.
    - simpl. apply ev_SS. exact H.
Qed.


Theorem ev_even_iff : forall (n:nat),
    ev n <-> exists k, n = double k.
Proof.
    intros n. split.
    - exact (ev_even n).
    - intros [k H]. rewrite H. apply ev_double.
Qed.


Theorem ev_sum : forall (n m:nat),
    ev n -> ev m -> ev (n + m).
Proof.
    intros n m Hn. generalize m. clear m. induction Hn as [|n H IH].
    - simpl. intros m H. exact H.
    - intros m. intros H'. simpl. apply ev_SS. apply IH. exact H'.
Qed.




