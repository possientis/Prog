Require Import ZF.Binary.
Require Import ZF.Set.

(* Local property of being functional at point a.                               *)
Definition FunctionalAt (F:Binary) (a:U) : Prop :=
  forall y, forall z, F a y -> F a z -> y = z.

(* Being functional at a is compatible with class equivalence.                  *)
Proposition FunctionalAtEquivCompat : forall (F G:Binary) (a:U),
  F :~: G -> FunctionalAt F a -> FunctionalAt G a.
Proof.
  intros F G a H1. unfold FunctionalAt. intros H2 y z H3 H4.
  apply H2; apply H1; assumption.
Qed.
