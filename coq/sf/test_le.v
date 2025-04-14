Require Import nat.
Require Import le.


Example test_le1 : 3 <= 3.
Proof. apply le_n. Qed.

Example test_le2 : 3 <= 6.
Proof. apply le_S, le_S, le_S, le_n. Qed.

Inductive square_of : nat -> nat -> Prop :=
| sq : forall (n:nat), square_of n (n * n)
.

Inductive next_nat : nat -> nat -> Prop :=
| nn : forall (n:nat), next_nat n (S n)
.

(*
Inductive next_even : nat -> nat -> Prop :=
| ne_1 : forall (n:nat), ev (S n) -> next_even n (S n)
| ne_2 : forall (n:nat), ev (S (S n)) -> next_even n (S (S n))
.
*)

Inductive total_rel : nat -> nat -> Prop :=
| tr : forall (n m:nat), total_rel n m
.

Example test_total_rel1 : forall (n m:nat), total_rel n m.
Proof. intros n m. apply tr. Qed.

Inductive empty_rel : nat -> nat -> Prop := .


Example test_empty_rel : forall (n m:nat), ~ (empty_rel n m).
Proof. intros n m H. inversion H. Qed.
