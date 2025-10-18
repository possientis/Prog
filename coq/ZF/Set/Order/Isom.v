Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Eval.

Module COI := ZF.Class.Order.Isom.

(* f is an (r,s)-isomorphism from a to b.                                       *)
Definition Isom (f r s a b:U) : Prop := Bij f a b /\ forall x y,
  x :< a             ->
  y :< a             ->
  :(x,y): :< r      <->
  :(f!x,f!y): :< s.

Proposition ToClass : forall (f r s a b:U),
  Isom f r s a b                                                        <->
  COI.Isom (toClass f) (toClass r) (toClass s) (toClass a) (toClass b).
Proof.
  intros f r s a b.
  split; intros [H1 H2]; split; try assumption; apply Bij.ToClass; assumption.
Qed.

