Require Import ZF.Class.
Require Import ZF.Core.And.

(* The intersection of two classes P and Q.                                     *)
Definition intersect (P Q:Class) : Class := fun x => P x /\ Q x.

(* Notation "P :/\: Q" := (intersect P Q)                                       *)
Global Instance ClassAnd : And Class := { and := intersect }.
