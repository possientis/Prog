Require Import ZF.Binary.

(* Predicate expressing the fact that a binary class is functional.             *)
Definition Functional (F:Binary) : Prop :=
  forall x, forall y, forall z, F x y -> F x z -> y = z.
