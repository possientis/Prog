Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Irreflexive.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

Module COI := ZF.Class.Order.Irreflexive.

(* Predicate expressing the fact that r is an irreflexive set on a.             *)
Definition Irreflexive (r a:U) : Prop := forall (x:U), x :< a -> ~ :(x,x): :< r.

Proposition ToClass : forall (r a:U),
  Irreflexive r a <-> COI.Irreflexive (toClass r) (toClass a).
Proof.
  intros r a. split; intros H1; assumption.
Qed.


