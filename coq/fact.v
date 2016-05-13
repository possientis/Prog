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

Check well_founded_ind.
(*
well_founded_ind
  : forall (A : Type) (R : A -> A -> Prop),
    well_founded R ->
    forall P : A -> Prop,
    (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
     forall a : A, P a

*)

Check Zwf_well_founded.
(*
Zwf_well_founded
     : forall c : Z, well_founded (Zwf c)
*)

(*
SearchPattern (_ < _ \/ _ = _).
Zle_lt_or_eq: forall n m : Z, n <= m -> n < m \/ n = m
*)


Lemma Zle_Pfact: forall x:Z, 0 <= x -> exists y:Z, Pfact x y.
Proof.
  intros x0.
  elim x0 using (well_founded_ind (Zwf_well_founded 0)).
  clear x0.
  intros x H H'. elim (Zle_lt_or_eq _ _ H').
  intro Hlt. elim (H (x-1)).
  intros  y' H0. exists (x*y'). apply Pfact1 with (n:=x)(v:=y').
  auto with zarith. exact H0. unfold Zwf. omega. omega.
  intro H0. exists 1. rewrite <- H0. apply Pfact0.
Qed.






