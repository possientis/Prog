Require Import ZF.Set.Core.

(* A binary class is simply a binary predicate on sets.                         *)
Definition Binary : Type := U -> U -> Prop.

(* Predicate expressing the fact that a binary class is functional.             *)
Definition Functional (F:Binary) : Prop :=
  forall x y z, F x y -> F x z -> y = z.

(* Given a functional binary class F and a set a, there exist a set b whose     *)
(* elements are the images of the elements of a by F.                           *)
Axiom Replacement : forall (F:Binary), Functional F ->
  forall a, exists b, forall y, y :< b <-> exists x, x :< a /\ F x y.
