Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Functional set.                                                              *)
Definition Functional (a:U) : Prop :=
  forall x y z, :(x,y): :< a -> :(x,z): :< a -> y = z.
