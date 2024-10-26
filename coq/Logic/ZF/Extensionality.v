Require Import Logic.ZF.Core.

(* If two sets have the same elements, then they are equal                      *)
Axiom Extensionality : forall a b, (forall x, x :< a <-> x :< b) -> a = b.

(* If two sets are characterised by the same predicate, then they are equal.    *)
Proposition SameCharacEqual : forall (P:U -> Prop), forall a b,
  (forall x, x :< a <-> P x) ->
  (forall x, x :< b <-> P x) ->
  a = b.
Proof.
  intros P a b Ha Hb. apply Extensionality. intros x. split.
  - intros H. apply Hb, Ha, H.
  - intros H. apply Ha, Hb, H.
Qed.


