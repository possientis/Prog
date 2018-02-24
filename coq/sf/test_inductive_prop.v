Require Import nat.
Require Import bool.
Require Import induction.

Require Import inductive_prop.


Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. exact ev_0. Qed.


Theorem ev_4' : ev 4.
Proof. exact (ev_SS 2 (ev_SS 0 ev_0)). Qed.


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


Theorem evSS_ev_fail : forall (n:nat),
    ev (S (S n)) -> ev n.
Proof.
    intros n H. destruct H as [|n' H'].
    Abort.

Theorem SSSSeven_even : forall (n:nat),
    ev (S (S (S (S n)))) -> ev n.
Proof. intros n H. inversion H as [|n' [|n'' H'']]. exact H''. Qed.

Theorem ev_even_fail : forall (n:nat),
    ev n -> exists k, n = double k.
Proof.
    intros n H. inversion H as [|n' H'].
    - exists 0. reflexivity.
    - assert (I: (exists k', n' = double k') -> (exists k, S (S n') = double k)).
        { intros [k' H1]. exists (S k'). rewrite H1. reflexivity. }
        apply I. Abort.

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

Theorem ev_ev__ev: forall (n m:nat),
    ev (n + m) -> ev n -> ev m.
Proof.
    intros n m Hnm Hn. generalize Hnm. clear Hnm. generalize m. clear m.
    induction Hn as [|n H H'].
    - intros m Hm. exact Hm.
    - simpl. intros m H0. apply H'. apply evSS_ev. exact H0.
Qed.

(* too much hassle right now 
Theorem ev_plus_plus : forall (n m p:nat),
    ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
    intros n m p Hnm Hnp.


Show.
*)


Inductive R : nat -> nat -> nat -> Prop :=
    | c1 : R 0 0 0 
    | c2 : forall (n m p:nat), R n m p -> R (S n) m (S p)
    | c3 : forall (n m p:nat), R n m p -> R n (S m) (S p)
    | c4 : forall (n m p:nat), R (S n) (S m) (S (S p)) -> R n m p
    | c5 : forall (n m p:nat), R n m p -> R m n p
    .

Lemma R_1_1_2 : R 1 1 2.
Proof. apply c3, c2, c1. Qed.


Lemma R_n_Sm : forall (n m p:nat), R n (S m) p -> R (S n) m p.
Proof. intros n m p H. apply c4, c2, c2. exact H. Qed.


Theorem R_equiv_plus : forall (n m p:nat), R n m p <-> n + m = p.
Proof.
    intros n m p. split.
    - intros H. induction H as [|n m p H IH|n m p H IH|n m p H IH|n m p H IH].
        + reflexivity.
        + simpl. rewrite IH. reflexivity.
        + rewrite plus_n_Sm. rewrite IH. reflexivity.
        + simpl in IH. rewrite plus_n_Sm in IH. inversion IH. reflexivity.
        + rewrite plus_comm. exact IH.
    - generalize m, p. clear m p. induction n as [|n H].
        + intros m p. simpl. intros H. rewrite H. clear H m. induction p as [|p H].
            { apply c1. }
            { apply c3. exact H. }
        + intros m p H'. apply R_n_Sm. apply H. rewrite plus_n_Sm. exact H'.
Qed.


Theorem ev_4'' : ev 4.
Proof.
(* Show Proof. *)
apply ev_SS.
(* Show Proof. *)
apply ev_SS.
(* Show Proof. *)
apply ev_0.
(* Show Proof. *)
Qed.

Definition ev_4''' : ev 4 := ev_SS 2 (ev_SS 0 ev_0).

(*
Print ev_4.
Print ev_4'.
Print ev_4''.
Print ev_4'''.
*)

Theorem ev_8 : ev 8.
Proof. apply ev_SS, ev_SS, ev_SS, ev_SS, ev_0. Qed.

Definition ev_8' : ev 8 := ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).

(*
Print ev_8.
Print ev_8'.
*)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof. intros n H. apply ev_SS, ev_SS. exact H. Qed.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
    fun (n:nat) (p:ev n) => ev_SS (2 + n) (ev_SS n p).

Definition ev_plus4'' (m:nat) (q:ev m) : ev (4 + m) :=
    ev_SS (2 + m) (ev_SS m q).

(*
Print ev_plus4.
Print ev_plus4'.
Print ev_plus4''.
*)

Lemma test1 : ev_plus4' = ev_plus4''.
Proof. reflexivity. Qed.

Definition ev_plus2 : Prop := forall n, forall (E:ev n), ev (n + 2).

Definition ev_plus2' : Prop := forall n, ev n -> ev (n + 2).

Lemma test2 : ev_plus2 = ev_plus2'. 
Proof. reflexivity. Qed.






