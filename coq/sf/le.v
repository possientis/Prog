Require Import inductive_prop.

Module LEMODULE.

Inductive le : nat -> nat -> Prop :=
| le_n : forall (n:nat), le n n
| le_S : forall (n m:nat), le n m -> le n (S m)
.

Notation "n <= m" := (le n m).


Example test_le1 : 3 <= 3.
Proof. apply le_n. Qed.

Example test_le2 : 3 <= 6.
Proof. apply le_S, le_S, le_S, le_n. Qed. 

Example test_le3 : (2 <= 1) -> 2 + 2 = 5.
Proof. intros H. inversion H as [|n m]. inversion H0. Qed.

Definition lt (n m:nat) : Prop := le (S n) m.

End LEMODULE.



Inductive square_of : nat -> nat -> Prop :=
| sq : forall (n:nat), square_of n (n * n)
.

Inductive next_nat : nat -> nat -> Prop :=
| nn : forall (n:nat), next_nat n (S n)
.

Inductive next_even : nat -> nat -> Prop :=
| ne_1 : forall (n:nat), ev (S n) -> next_even n (S n)
| ne_2 : forall (n:nat), ev (S (S n)) -> next_even n (S (S n))
.


Inductive total_rel : nat -> nat -> Prop :=
| tr : forall (n m:nat), total_rel n m
.

Example test_total_rel1 : forall (n m:nat), total_rel n m.
Proof. intros n m. apply tr. Qed.

Inductive empty_rel : nat -> nat -> Prop := .

Example test_empty_rel : forall (n m:nat), ~ (empty_rel n m).
Proof. intros n m H. inversion H. Qed.


(* induction on proofs *)
Lemma le_trans : forall (n m p:nat), 
    n <= m -> m <= p -> n <= p.
Proof.
    intros n m p H. generalize p. clear p.
    induction H as [n'|n' H0 H'].
    - intros p H'. exact H'.
    - intros p H1. induction H1 as [p'| p' H2 H3].
        + apply H'. apply le_S, le_n.
        + apply le_S. exact H3.
Qed.

Lemma le_0_n : forall (n:nat), 0 <= n.
Proof. 
    induction n as [|n H].
    - apply le_n.
    - apply le_S. exact H.
Qed.

Theorem n_le_m__Sn_le_Sm : forall (n m:nat),
    n <= m -> S n <= S m.
Proof.
    intros n m H. induction H as [n'|n' m H'].
    - apply le_n.
    - apply le_S. exact H'.
Qed.

(*
Theorem Sn_le_Sm__n_le_m : forall (n m:nat),
    S n <= S m -> n <= m.
Proof.


Show.
*)

