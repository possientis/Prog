Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.

(* A set is a bijection iff it is a relation and it is one-to-one.              *)
Definition Bijection (f:U) : Prop := Relation f /\ OneToOne f.

(* A bijection is a function.                                                   *)
Proposition IsFunction : forall (f:U),
  Bijection f -> Function f.
Proof.
  intros f [H1 [H2 _]]. split; assumption.
Qed.

(* Two bijections are equal iff they have same domain and coincide pointwise.   *)
Proposition EqualCharac : forall (f g:U),
  Bijection f                             ->
  Bijection g                             ->
  domain f = domain g                     ->
  (forall x, x :< domain f -> f!x = g!x)  ->
  f = g.
Proof.
  intros f g H1 H2. apply Function.EqualCharac; apply IsFunction; assumption.
Qed.

(* f need not be a bijection.                                                   *)
Proposition ImageOfDomain : forall (f:U),
  f:[domain f]: = range f.
Proof.
  apply Range.ImageOfDomain.
Qed.
