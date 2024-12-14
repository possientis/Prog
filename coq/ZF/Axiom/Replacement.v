Require Import ZF.Binary.
Require Import ZF.Binary.Functional.
Require Import ZF.Set.

(* Given a functional binary class F and a set a, there exist a set b whose     *)
(* elements are the images of the elements of a by F.                           *)
Axiom Replacement : forall (F:Binary), Functional F ->
  forall a, exists b, forall y, y :< b <-> exists x, x :< a /\ F x y.
