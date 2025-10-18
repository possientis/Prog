Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.AntiSymmetric.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

Module COA := ZF.Class.Order.AntiSymmetric.

(* Predicate expressing the fact that r is an anti-symmetric set on a.          *)
Definition AntiSymmetric (r a:U) : Prop := forall (x y:U), x :< a -> y :< a ->
  :(x,y): :< r -> :(y,x): :< r -> x = y.

Proposition ToClass : forall (r a:U),
  AntiSymmetric r a <-> COA.AntiSymmetric (toClass r) (toClass a).
Proof.
  intros r a. split; intros H1 x y; apply H1.
Qed.
