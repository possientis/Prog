Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.AntiSymmetric.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Order.Transport.
Require Import ZF.Set.Relation.Bij.

Module COA := ZF.Class.Order.AntiSymmetric.

(* Predicate expressing the fact that r is an anti-symmetric set on a.          *)
Definition AntiSymmetric (r a:U) : Prop := forall (x y:U), x :< a -> y :< a ->
  :(x,y): :< r -> :(y,x): :< r -> x = y.

Proposition ToClass : forall (r a:U),
  AntiSymmetric r a -> COA.AntiSymmetric (toClass r) (toClass a).
Proof.
  intros r a H1. assumption.
Qed.

Proposition FromClass : forall (r a:U),
  COA.AntiSymmetric (toClass r) (toClass a) -> AntiSymmetric r a.
Proof.
  intros r a H1. assumption.
Qed.

(* Anti-symmetry is preserved under transport by a bijection.                   *)
Proposition Transport : forall (f r s a b:U),
  s = transport f r a  ->
  Bij f a b            ->
  AntiSymmetric r a    ->
  AntiSymmetric s b.
Proof.
  (* Proof by Claude.                                                           *)
  intros f r s a b H1 H2 H3 y1 y2 H4 H5 H6 H7.
  apply (Bij.RangeCharac f a b) in H4. 2: assumption.
  apply (Bij.RangeCharac f a b) in H5. 2: assumption.
  destruct H4 as [x1 [H4 H8]]. destruct H5 as [x2 [H5 H9]].
  rewrite <- H8, <- H9 in H6. rewrite H1 in H6.
  rewrite <- H9, <- H8 in H7. rewrite H1 in H7.
  apply (Transport.Charac2f f r a b) in H6. 2-4: assumption.
  apply (Transport.Charac2f f r a b) in H7. 2-4: assumption.
  assert (x1 = x2) as H10. { apply H3; assumption. }
  rewrite <- H8, <- H9. rewrite H10. reflexivity.
Qed.
