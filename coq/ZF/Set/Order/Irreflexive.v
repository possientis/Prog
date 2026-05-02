Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Irreflexive.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Order.Transport.
Require Import ZF.Set.Relation.Bij.

Module COI := ZF.Class.Order.Irreflexive.

(* Predicate expressing the fact that r is an irreflexive set on a.             *)
Definition Irreflexive (r a:U) : Prop := forall (x:U), x :< a -> ~ :(x,x): :< r.

Proposition ToClass : forall (r a:U),
  Irreflexive r a -> COI.Irreflexive (toClass r) (toClass a).
Proof.
  intros r a H1. assumption.
Qed.

Proposition FromClass : forall (r a:U),
  COI.Irreflexive (toClass r) (toClass a) -> Irreflexive r a.
Proof.
  intros r a H1. assumption.
Qed.

(* Irreflexivity is preserved under transport by a bijection.                   *)
Proposition Transport : forall (f r s a b:U),
  s = transport f r a ->
  Bij f a b           ->
  Irreflexive r a     ->
  Irreflexive s b.
Proof.
  (* Proof by Claude.                                                           *)
  intros f r s a b H1 H2 H3 y H4 H5.
  apply (Bij.RangeCharac f a b) in H4. 2: assumption.
  destruct H4 as [x [H4 H6]].
  rewrite <- H6 in H5. rewrite H1 in H5.
  apply (Transport.Charac2f f r a b) in H5. 2-4: assumption.
  revert H5. apply H3. assumption.
Qed.
