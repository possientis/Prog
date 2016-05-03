Require Import List. 
Require Import Arith.

Inductive sorted {A:Set}(R:A->A->Prop) : list A -> Prop :=
  | sorted0       : sorted R nil
  | sorted1       : forall x:A, sorted R (cons x nil)
  | sorted2       : forall (x y:A)(l:list A),
                      R x y -> sorted R (cons y l) -> sorted R (cons x (cons y l)).


Inductive sorted' {A:Set}{R:A->A->Prop} : list A -> Prop :=
  | sorted0_2     : sorted' nil
  | sorted1_2     : forall x:A, sorted' (cons x nil)
  | sorted2_2     : forall (x y:A)(l:list A),
                      R x y -> sorted' (cons y l) -> sorted' (cons x (cons y l)).


Check sorted_ind.
(*
forall (A : Set) (R : A -> A -> Prop) (P : list A -> Prop),
P nil ->
(forall x : A, P (x :: nil)) ->
(forall (x y : A) (l : list A),
R x y -> sorted R (y :: l) -> P (y :: l) -> P (x :: y :: l)) ->
forall l : list A, sorted R l -> P l
*)

(* yet, when writing sorted' l... there is no way to know what R is *)
(* whereas the type A is implicit from the type of l                *)
(* How can coq cope? *)
Check sorted'_ind.
(*
forall (A : Set) (R : A -> A -> Prop) (P : list A -> Prop),
P nil ->
(forall x : A, P (x :: nil)) ->
(forall (x y : A) (l : list A),
R x y -> sorted' (y :: l) -> P (y :: l) -> P (x :: y :: l)) ->
forall l : list A, sorted' l -> P l
*)

Lemma example_sorted1 : sorted le (1::2::3::nil). 
Proof.
  (* auto will fail at this stage *)
  apply sorted2. auto. (* for 1 <= 2 *)
  apply sorted2. auto. (* for 2 <= 3 *)
  apply sorted1.
Qed.


Hint Resolve sorted0 sorted1 sorted2: sorted_base.
Lemma example_sorted2 : sorted le (1::2::3::nil).
Proof.
  auto with sorted_base. (* Hurray !!! *)
Qed.

Lemma example_sorted3 : forall x y:nat, le x y -> sorted le (x::y::nil). 
Proof.
  auto with sorted_base. (* Hurray !!!! *)
Qed.

Lemma example_sorted4 : forall l:list nat, sorted le l -> sorted le (cons 0 l).
Proof.
  induction 1. (* induction on second hyp ??? *)
  auto with sorted_base.
  auto with sorted_base arith. (* need arith here for some reason *)
  auto with sorted_base arith. (* need arith here for some reason *)

