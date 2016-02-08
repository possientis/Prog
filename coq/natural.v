Require Import List.

(*Require Import CpdtTactics.*)

Set Implicit Arguments.

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Fixpoint plus (n m : nat) : nat :=
match n with
  | O => m
  | S n' => S (plus n' m)
end.

Theorem O_plus_n : forall n:nat, plus O n = n.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem n_plus_O : forall n:nat, plus n O = n.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem plus_assoc_from_left : forall n m p : nat, 
  plus (plus n m) p = plus n (plus m p).
  induction n.
  simpl.
  reflexivity.
  simpl.
  intros. 
  rewrite IHn.
  reflexivity.
Qed.

Theorem plus_assoc_from_right : forall n m p : nat, 
  plus n (plus m p) = plus (plus n m) p.
  induction n.
  simpl.
  reflexivity.
  intros.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma plus_succ_inside : forall n m : nat,
  S(plus n m) = plus n (S m).
  induction n.
  simpl.
  reflexivity.
  simpl.
  intros.
  rewrite IHn.
  reflexivity.
Qed.


Theorem plus_commutativity : forall n m : nat,
  plus n m = plus m n.

  induction n.
  simpl.
  intros.
  rewrite n_plus_O.
  reflexivity.
  simpl.
  intros.
  rewrite IHn.
  apply plus_succ_inside.
Qed.

Fixpoint mult (n m : nat) : nat :=
match n with
  | O => O
  | S n' => plus (mult n' m) m
end.

Definition I : nat := S O.

Theorem n_plus_I : forall n:nat, plus n I = S n.
  induction n.
  simpl.
  unfold I.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem I_mult_n : forall n:nat, mult I n = n.
  simpl.
  reflexivity.
Qed.


Theorem n_mult_I : forall n:nat, mult n I = n.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  simpl.
  apply n_plus_I.
Qed.

Lemma n_mult_O : forall n:nat, mult n O = O.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  simpl.
  reflexivity.
Qed.


Theorem right_distributivity : forall n m p : nat,
  mult (plus n m) p = plus (mult n p) (mult m p).
  induction n.
  simpl.
  reflexivity.
  simpl.
  intros.
  rewrite IHn.
  rewrite plus_assoc_from_left.

(*
Theorem mult_assoc_from_left: forall n m p :nat,
  mult (mult n m) p = mult n (mult m p).
  induction n
  intros.
  simpl.
  reflexivity.
  simpl.
*)



