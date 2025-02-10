Require Import ZF.Class.
Require Import ZF.Class.Bij.
Require Import ZF.Class.I.
Require Import ZF.Class.Restrict.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* H is an isomorphism from A to B w.r. to R and S.                             *)
Definition Isom (H R S A B:Class) : Prop := Bij H A B /\ forall x y, A x -> A y ->
  R :(x,y): <-> S :(H!x,H!y):.

(* The restriction of I to A is an isomorphism from A to A w.r to R.            *)
Proposition IsomI : forall (R A:Class), Isom (I:|:A) R R A A.
Proof.
  intros R A. split.
  -
Admitted.

