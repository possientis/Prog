Require Import ZF.Set.

(* Given a set a, there exists a set b whose elements are the elements of all   *)
(* the elements of a. More formally:                                            *)
Axiom Union : forall a, exists b, forall x, x :< b <-> exists y, x :< y /\ y :< a.
