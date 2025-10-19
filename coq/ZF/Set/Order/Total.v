Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Total.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

Module COT := ZF.Class.Order.Total.

(* Predicate expressing the fact that r is a total set on a.                    *)
Definition Total (r a:U) : Prop := forall (x y:U), x :< a -> y :< a ->
  x = y \/ :(x,y): :< r \/ :(y,x): :< r.

Proposition ToClass : forall (r a:U),
  Total r a <-> COT.Total (toClass r) (toClass a).
Proof.
  intros r a . split; intros H1; assumption.
Qed.
