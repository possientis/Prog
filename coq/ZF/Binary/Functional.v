Require Import ZF.Binary.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.

(* Predicate expressing the fact that a binary class is functional.             *)
Definition Functional (F:Binary) : Prop :=
  forall x, forall y, forall z, F x y -> F x z -> y = z.

Proposition FunctionalEquivCompat : forall (F G:Binary),
  F :~: G -> Functional F -> Functional G.
Proof.
  unfold Functional. intros F G H1 H2 x y z H3 H4. apply BinaryEquivSym in H1.
  apply H2 with x; apply H1; assumption.
Qed.
