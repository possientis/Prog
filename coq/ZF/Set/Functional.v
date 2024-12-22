Require Import ZF.Class.Functional.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Functional set.                                                              *)
Definition Functional (a:U) : Prop
  := Class.Functional.Functional (toClass a).

Proposition FunctionalCharac : forall (a:U),
  Functional a <-> (forall x y z, :(x,y): :< a -> :(x,z): :< a -> y = z).
Proof.
  intros a. apply Class.Functional.FunctionalCharac.
Qed.
