Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Reflexive.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Order.Transport.
Require Import ZF.Set.Relation.Bij.

Module COR := ZF.Class.Order.Reflexive.

(* Predicate expressing the fact that r is a reflexive set on a.                *)
Definition Reflexive (r a:U) : Prop := forall (x:U), x :< a -> :(x,x): :< r.

Proposition ToClass : forall (r a:U),
  Reflexive r a -> COR.Reflexive (toClass r) (toClass a).
Proof.
  intros r a H1. assumption.
Qed.

Proposition FromClass : forall (r a:U),
  COR.Reflexive (toClass r) (toClass a) -> Reflexive r a.
Proof.
  intros r a H1. assumption.
Qed.

(* Reflexivity is preserved under transport by a bijection.                     *)
Proposition Transport : forall (f r s a b:U),
  s = transport f r a ->
  Bij f a b           ->
  Reflexive r a       ->
  Reflexive s b.
Proof.
  (* Proof by Claude.                                                           *)
  intros f r s a b H1 H2 H3 y H4.
  apply (Bij.RangeCharac f a b) in H4. 2: assumption.
  destruct H4 as [x [H4 H5]].
  rewrite <- H5. rewrite H1.
  apply (Transport.Charac2f f r a b). 1-3: assumption. apply H3. assumption.
Qed.

