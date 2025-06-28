Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Relation.FunctionalAt.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* A functional class.                                                          *)
Definition Functional (F:Class) : Prop :=
  forall x y z, F :(x,y): -> F :(x,z): -> y = z.

(* Being functional is compatible with class equivalence.                       *)
Proposition EquivCompat : forall (F G:Class),
  F :~: G -> Functional F -> Functional G.
Proof.
  intros F G H1 H2 x y z H3 H4. apply (H2 x); apply H1; assumption.
Qed.

(* Being functional is compatible with class inclusion (not quite of course).   *)
Proposition InclCompat : forall (F G:Class),
  F :<=: G -> Functional G -> Functional F.
Proof.
  intros F G H1 H2 x y z H3 H4. apply (H2 x); apply H1; assumption.
Qed.

(* A functional class is functional at all points.                              *)
Proposition IsFunctionalAt : forall (F:Class),
  Functional F <-> forall a, FunctionalAt F a.
Proof.
  intros F. split; intros H1.
  - intros a y z. apply H1.
  - intros x. apply H1.
Qed.

