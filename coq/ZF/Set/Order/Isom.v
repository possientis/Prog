Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Eval.

Require Import ZF.Notation.Eval.

Module COI := ZF.Class.Order.Isom.

(* f is an (r,s)-isomorphism from a to b.                                       *)
Definition Isom (f r s a b:U) : Prop := Bij f a b /\ forall x y,
  x :< a             ->
  y :< a             ->
  :(x,y): :< r      <->
  :(f!x,f!y): :< s.

Proposition ToClass : forall (f r s a b:U),
  Isom f r s a b ->
  COI.Isom (toClass f) (toClass r) (toClass s) (toClass a) (toClass b).
Proof.
  intros f r s a b [H1 H2]. split. 2: assumption.
  apply Bij.ToClass. assumption.
Qed.

Proposition FromClass : forall (f r s a b:U),
  COI.Isom (toClass f) (toClass r) (toClass s) (toClass a) (toClass b) ->
  Isom f r s a b.
Proof.
  intros f r s a b [H1 H2]. split. 2: assumption.
  apply Bij.FromClass. assumption.
Qed.

(* The inverse of an isomorphism is an isomorphism for the reversed orders.     *)
Proposition Converse : forall (f r s a b:U),
  Isom f r s a b -> Isom f^:-1: s r b a.
Proof.
  (* Proof by Claude.                                                           *)
  intros f r s a b H1. apply FromClass.
  apply COI.EquivCompat1 with (toClass f)^:-1:.
  - apply Equiv.Sym. apply Converse.ToClass.
  - apply COI.Converse. apply ToClass. exact H1.
Qed.
