Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Inter2.

(* Every non-empty set a has an element which does not contain any element of a.*)
Axiom Foundation : forall a, a <> :0: -> exists x, x :< a /\ x :/\: a = :0:.
