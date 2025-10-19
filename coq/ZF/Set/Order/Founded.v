Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Founded.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.Minimal.

Module COF := ZF.Class.Order.Founded.

(* Predicate expressing the fact that r is a founded set on a.                  *)
(* r is founded on a iff every non-empty subset of a has an r-minimal element.  *)
Definition Founded (r a:U) : Prop := forall b,
  b :<=: a                  ->
  b <> :0:                  ->
  exists x, Minimal r b x.

Proposition ToClass : forall (r a:U),
  Founded r a <-> COF.Founded (toClass r) (toClass a).
Proof.
  intros r a. split; intros H1 b H2 H3; apply H1; assumption.
Qed.
