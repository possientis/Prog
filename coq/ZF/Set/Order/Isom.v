Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Order.Transport.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Compose.
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

(* The composition of two isomorphisms is an isomorphism.                       *)
Proposition Compose : forall (f g r s t a b c:U),
  Isom f r s a b ->
  Isom g s t b c ->
  Isom (g :.: f) r t a c.
Proof.
  (* Proof by Claude.                                                           *)
  intros f g r s t a b c [H1 H2] [H3 H4]. split.
  - apply Bij.Compose with b; assumption.
  - intros x y H5 H6. split; intros H7.
    + rewrite (Bij.ComposeEval f g a b c x); try assumption.
      rewrite (Bij.ComposeEval f g a b c y); try assumption.
      apply H4. 3: apply H2; try assumption.
      * apply (Bij.IsInRange f a b); assumption.
      * apply (Bij.IsInRange f a b); assumption.
    + apply H2; try assumption. apply H4.
      * apply (Bij.IsInRange f a b); assumption.
      * apply (Bij.IsInRange f a b); assumption.
      * rewrite (Bij.ComposeEval f g a b c x) in H7; try assumption.
        rewrite (Bij.ComposeEval f g a b c y) in H7; try assumption.
Qed.

(* If s is the transport of r by f, then f is an (r,s)-isomorphism.             *)
Proposition Transport : forall (f r s a b:U),
  s = transport f r a ->
  Bij f a b           ->
  Isom f r s a b.
Proof.
  (* Proof by Claude.                                                           *)
  intros f r s a b H1 H2. split. 1: assumption.
  intros x y H3 H4. rewrite H1.
  split; intro H5; apply (Transport.Charac2f f r a b); assumption.
Qed.
