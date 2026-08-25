Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.


(* Given a functional class F and a set a, there exists a set b whose elements  *)
(* are the images of the elements of a by F.                                    *)
Axiom Replacement : forall (F:Class), Functional F ->
  forall a, exists b, forall y, y :< b <-> exists x, x :< a /\ F :(x,y):.
