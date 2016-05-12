Require Import Zwf.
Require Import ZArith.
Open Scope Z_scope.

(* defining factorial function as an inductive predicate *)
(* using Z instead of nat to highlight possible non termination *)

Inductive Pfact : Z -> Z -> Prop :=
  | Pfact0 : Pfact 0 1  (* fact 0 = 1 *)
  | Pfact1 : forall n v:Z, n <> 0 -> Pfact (n-1) v -> Pfact n (n*v).

Lemma pfact3: Pfact 3 6.
Proof.
  apply Pfact1 with (n:=3)(v:=2). discriminate.
  apply Pfact1 with (n:=2)(v:=1). discriminate.
  apply Pfact1 with (n:=1)(v:=1). discriminate.
  apply Pfact0.
Qed.

Lemma fact_def_pos: forall x y:Z, Pfact x y -> 0 <= x.
Proof.
  intros x y H. elim H. auto with zarith.
  intros n v H0 H1 H2. omega.
Qed.

Print Zwf.
(*
Zwf = fun c x y : Z => c <= y /\ x < y
     : Z -> Z -> Z -> Prop
*)

Print well_founded.
(*
well_founded = 
fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
     : forall A : Type, (A -> A -> Prop) -> Prop
*)

Print Acc.
(*
Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x
*)




