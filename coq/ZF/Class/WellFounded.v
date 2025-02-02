Require Import ZF.Class.
Require Import ZF.Class.Founded.
Require Import ZF.Class.InitSegment.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Small.
Require Import ZF.Set.

(* Predicate expressing the fact that R is a well-founded class on A.           *)
(* R is well-founded on A iff it is founded on A and all traces on A of initial *)
(* segments are small.                                                          *)
Definition WellFounded (R A:Class) : Prop :=
  Founded R A /\ forall (a:U), A a -> Small (initSegment R A a).

