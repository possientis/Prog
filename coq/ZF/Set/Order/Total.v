Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Total.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.Transport.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Bij.

Module COT := ZF.Class.Order.Total.

(* Predicate expressing the fact that r is a total set (as relation) on a.      *)
Definition Total (r a:U) : Prop := forall (x y:U), x :< a -> y :< a ->
  x = y \/ :(x,y): :< r \/ :(y,x): :< r.

(* If the sets form a total pair, then so do the classes.                       *)
Proposition ToClass : forall (r a:U),
  Total r a -> COT.Total (toClass r) (toClass a).
Proof.
  intros r a H1. assumption.
Qed.

(* If the classes form a total pair, then so do the sets.                       *)
Proposition FromClass : forall (r a:U),
  COT.Total (toClass r) (toClass a) -> Total r a.
Proof.
  intros r a H1. assumption.
Qed.

(* Totality on a restricts to totality on any subset b.                         *)
Proposition InclCompat : forall (r a b:U),
  b :<=: a -> Total r a -> Total r b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* Elements of b are elements of a, so the larger-domain property applies.    *)
  intros r a b H1 H2 x y H3 H4. apply H2; apply H1; assumption.
Qed.

(* Totality is preserved under transport by a bijection.                        *)
Proposition Transport : forall (f r s a b:U),
  s = transport f r a ->
  Bij f a b           ->
  Total r a           ->
  Total s b.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros f r s a b H1 H2 H3 y1 y2 H4 H5.
  apply (Bij.RangeCharac f a b) in H4. 2: assumption.
  apply (Bij.RangeCharac f a b) in H5. 2: assumption.
  destruct H4 as [x1 [H4 H6]]. destruct H5 as [x2 [H5 H7]].
  assert (x1 = x2 \/ :(x1,x2): :< r \/ :(x2,x1): :< r) as H8.
  { apply H3; assumption. }
  destruct H8 as [H8|[H8|H8]]; rewrite <- H6, <- H7.
  - left. rewrite H8. reflexivity.
  - right. left. rewrite H1. apply (Transport.Charac2f f r a b); assumption.
  - right. right. rewrite H1. apply (Transport.Charac2f f r a b); assumption.
Qed.
