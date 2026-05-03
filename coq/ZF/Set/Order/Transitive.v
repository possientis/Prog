Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Transitive.
Require Import ZF.Set.Core.
Require Import ZF.Set.Order.Transport.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Bij.

Module COT := ZF.Class.Order.Transitive.

(* Predicate expressing the fact that r is a transitive set on a.               *)
Definition Transitive (r a:U) : Prop := forall (x y z:U),
  x :< a        ->
  y :< a        ->
  z :< a        ->
  :(x,y): :< r  ->
  :(y,z): :< r  ->
  :(x,z): :< r.

Proposition ToClass : forall (r a:U),
  Transitive r a -> COT.Transitive (toClass r) (toClass a).
Proof.
  intros r a H1. assumption.
Qed.

Proposition FromClass : forall (r a:U),
  COT.Transitive (toClass r) (toClass a) -> Transitive r a.
Proof.
  intros r a H1. assumption.
Qed.

(* Transitivity is preserved under transport by a bijection.                    *)
Proposition Transport : forall (f r s a b:U),
  s = transport f r a ->
  Bij f a b           ->
  Transitive r a      ->
  Transitive s b.
Proof.
  (* Proof by Claude.                                                           *)
  intros f r s a b H1 H2 H3 x y z H4 H5 H6 H7 H8.
  apply (Bij.RangeCharac f a b) in H4. 2: assumption.
  apply (Bij.RangeCharac f a b) in H5. 2: assumption.
  apply (Bij.RangeCharac f a b) in H6. 2: assumption.
  destruct H4 as [x1 [H4 H9]]. destruct H5 as [x2 [H5 H10]].
  destruct H6 as [x3 [H6 H11]].
  rewrite <- H9, <- H10 in H7. rewrite H1 in H7.
  rewrite <- H10, <- H11 in H8. rewrite H1 in H8.
  apply (Transport.Charac2f f r a b) in H7. 2-4: assumption.
  apply (Transport.Charac2f f r a b) in H8. 2-4: assumption.
  rewrite <- H9, <- H11. rewrite H1.
  apply (Transport.Charac2f f r a b). 1-3: assumption.
  apply H3 with x2; assumption.
Qed.
