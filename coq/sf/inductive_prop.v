Require Import nat.
Require Import bool.
Require Import not.
Require Import induction.

Inductive ev : nat -> Prop :=
    | ev_0  : ev 0
    | ev_SS : forall (n:nat), ev n -> ev (S (S n))
    . 

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. exact ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. exact (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall (n:nat), ev n -> ev (4 + n).
Proof. intros n H. apply ev_SS, ev_SS. exact H. Qed.


Theorem ev_double : forall n, ev (double n).
Proof.
    induction n as [|n H].
    - exact ev_0.
    - simpl. apply ev_SS. exact H.
Qed.


Theorem evenb_minus2 : forall (n:nat),
    evenb n = true -> evenb (pred (pred n)) = true.
Proof.
    intros n H. destruct n.
    - reflexivity.
    - simpl. destruct n.
        + inversion H.
        + simpl. simpl in H. exact H.
Qed.

Theorem evenb_minus2' : forall (n:nat),
    evenb n = true -> evenb (pred (pred n)) = true.
Proof.
    intros [|[|n]].
    - reflexivity.
    - intros H. inversion H.
    - simpl. intros H. exact H.
Qed.

Theorem ev_minus2 : forall (n:nat),
    ev n -> ev (pred (pred n)).
Proof.
    intros [|[|n]].
    - simpl. intros H. exact H.
    - simpl. intros _. apply ev_0.
    - simpl. Abort.

(* by induction on the proof of ev n *)
Theorem ev_minus2' : forall (n:nat),
    ev n -> ev (pred (pred n)).
Proof.
    intros n H. inversion H as [|n' H'].
    - apply ev_0.
    - exact H'.
Qed.

Theorem ev_minus2'' : forall (n:nat),
    ev n -> ev (pred (pred n)).
Proof.
    intros n H. destruct H as [|n H].
    - exact ev_0.
    - exact H.
Qed.


Theorem evSS_ev : forall (n:nat),
    ev (S (S n)) -> ev n.
Proof.
    intros n H. destruct H as [|n' H'].
    Abort.

Theorem evSS_ev' : forall (n:nat),
    ev (S (S n)) -> ev n.
Proof. intros n H. inversion H as [|n' H']. exact H'. Qed.


Theorem one_not_even : ¬ ev 1.
Proof. intros H. inversion H. Qed.

Theorem SSSSeven_even : forall (n:nat),
    ev (S (S (S (S n)))) -> ev n.
Proof. intros n H. inversion H as [|n' [|n'' H'']]. exact H''. Qed.

Theorem even5_nonsense : ev 5 -> 2 + 2 = 9.
Proof. 
    intros H. inversion H as [|n H']. inversion H' as [|n' H2]. 
    inversion H2. inversion H0.
Qed.

Theorem ev_even_fail : forall (n:nat),
    ev n -> exists k, n = double k.
Proof.
    intros n H. inversion H as [|n' H'].
    - exists 0. reflexivity.
    - assert (I: (exists k', n' = double k') -> (exists k, S (S n') = double k)).
        { intros [k' H1]. exists (S k'). rewrite H1. reflexivity. }
        apply I. Abort.

Theorem ev_even : forall (n:nat),
    ev n -> exists k, n = double k.
Proof.
    intros n H. induction H as [|n H [k H']].
    - exists 0. reflexivity.
    - exists (S k). simpl. rewrite <- H'. reflexivity.
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


Inductive ev' : nat -> Prop :=
    | ev'_0 : ev' 0
    | ev'_2 : ev' 2
    | ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m)
    .  

Theorem ev_ev' : forall (n:nat),
    ev' n <-> ev n.
Proof.
    intros n. split.
    - intros H. induction H as [| |n m H1 H2 H3 H4].
        + exact ev_0.
        + apply ev_SS. exact ev_0.
        + apply ev_sum. exact H2. exact H4.
    - intros H. induction H as [|n H1 H2].
        + exact ev'_0.
        + apply (ev'_sum 2 n).
            { exact ev'_2. }
            { exact H2. }
Qed.

(*
Theorem ev_ev__ev: forall (n m:nat),
    ev (n + m) -> ev n -> ev m.
Proof.


Show.
*)

