Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Reflexive.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

Module COR := ZF.Class.Order.Reflexive.

(* Predicate expressing the fact that r is a reflexive set on a.                *)
Definition Reflexive (r a:U) : Prop := forall (x:U), x :< a -> :(x,x): :< r.

Proposition ToClass : forall (r a:U),
  Reflexive r a <-> COR.Reflexive (toClass r) (toClass a).
Proof.
  intros r a. split; intros H1; assumption.
Qed.

