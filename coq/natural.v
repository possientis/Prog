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

Lemma O_mult_n : forall n:nat, mult O n = O.
  induction n.
  simpl.
  reflexivity.
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
  assert (plus (mult m p) p = plus p (mult m p)).
  rewrite plus_commutativity.
  reflexivity.
  rewrite H.
  rewrite plus_assoc_from_right.
  reflexivity.
Qed.

Theorem left_distributivity : forall n m p : nat,
  mult n (plus m p) = plus (mult n m) (mult n p).
  induction n.
  intros.
  simpl.
  reflexivity.
  intros.
  simpl.
  rewrite IHn.
  assert(plus (plus (mult n m) (mult n p)) (plus m p) 
    = plus (mult n m) (plus (mult n p) (plus m p))).
  rewrite plus_assoc_from_left.
  reflexivity.
  rewrite H.
  assert(plus (mult n p) (plus m p) = plus (plus (mult n p) m) p).
  rewrite plus_assoc_from_right.
  reflexivity.
  rewrite H0.
  assert(plus (mult n p) m = plus m (mult n p)).
  rewrite plus_commutativity.
  reflexivity.
  rewrite H1.
  assert(plus (plus (mult n m) m) (plus (mult n p) p) = plus (mult n m) (plus m (plus (mult n p) p))).
  rewrite plus_assoc_from_left.
  reflexivity.
  rewrite H2.
  rewrite plus_assoc_from_left.
  reflexivity.
Qed. 

Theorem mult_assoc_from_left: forall n m p :nat,
  mult (mult n m) p = mult n (mult m p).
  induction n.
  intros.
  simpl.
  reflexivity.
  intros.
  simpl.
  rewrite right_distributivity.
  rewrite IHn.
  reflexivity.
Qed.

Theorem mult_assoc_from_right: forall n m p :nat,
  mult n (mult m p) = mult (mult n m) p.
  induction n.
  intros.
  simpl.
  reflexivity.
  intros.
  simpl.
  rewrite IHn.
  rewrite right_distributivity.
  reflexivity.
Qed.

Theorem mult_commutativity: forall n m : nat,
  mult n m = mult m n.
  induction n.
  intro.
  simpl.
  rewrite n_mult_O.
  reflexivity.
  intro.
  simpl.
  rewrite IHn.
  assert(S n = plus n I).
  rewrite n_plus_I.
  reflexivity.
  rewrite H.
  rewrite left_distributivity.
  rewrite n_mult_I.
  reflexivity.
Qed.

