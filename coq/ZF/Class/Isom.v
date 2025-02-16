Require Import ZF.Class.
Require Import ZF.Class.Bij.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Restrict.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* H is an isomorphism from A to B w.r. to R and S.                             *)
Definition Isom (H R S A B:Class) : Prop := Bij H A B /\ forall x y, A x -> A y ->
  R :(x,y): <-> S :(H!x,H!y):.

Proposition ConverseIsIsom : forall (H R S A B:Class),
  Isom H R S A B -> Isom H^:-1: S R B A.
Proof.
  intros H R S A B [H1 H2]. split.
  - apply ConverseIsBij. assumption.
  - intros x y H3 H4. split; intros H5.
    + apply H2.


Admitted.
