Require Import ZF.Class.
Require Import ZF.Class.Bij.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Restrict.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* H is an isomorphism from A to B w.r. to R and S.                             *)
Definition Isom (F R S A B:Class) : Prop := Bij F A B /\ forall x y, A x -> A y ->
  R :(x,y): <-> S :(F!x,F!y):.

Proposition ConverseIsIsom : forall (F R S A B:Class),
  Isom F R S A B -> Isom F^:-1: S R B A.
Proof.
  intros F R S A B [H1 H2]. split.
  - apply ConverseIsBij. assumption.
  - intros x y H3 H4. split; intros H5.
    + apply H2.
      * apply BijF_EvalIsInDomain with B; assumption.
      * apply BijF_EvalIsInDomain with B; assumption.
      * rewrite (BijFF_Eval F A B x), (BijFF_Eval F A B y); assumption.
    + rewrite <- (BijFF_Eval F A B x), <- (BijFF_Eval F A B y); try assumption.
      apply H2. 3: assumption.
      * apply BijF_EvalIsInDomain with B; assumption.
      * apply BijF_EvalIsInDomain with B; assumption.
Qed.
