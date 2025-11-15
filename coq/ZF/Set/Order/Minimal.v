Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.


Module COM := Class.Order.Minimal.

(* Predicate expressing the fact that b is an r-minimal element of a.           *)
Definition Minimal (r a b:U) : Prop
  := b :< a /\ (forall x, x :< a  -> ~ :(x,b): :< r).

Proposition ToClass : forall (r a b:U),
  Minimal r a b <-> COM.Minimal (toClass r) (toClass a) b.
Proof.
  intros r a b. split; intros [H1 H2]; split; assumption.
Qed.

Proposition IsIn : forall (r a b:U),
  Minimal r a b -> b :< a.
Proof.
  intros r a b H1. apply H1.
Qed.
