Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.FunctionalAt.

(* A functional set.                                                            *)
Definition Functional (a:U) : Prop :=
  forall x y z, :(x,y): :< a -> :(x,z): :< a -> y = z.

Proposition ToClass : forall (a:U),
  Functional a <-> Class.Relation.Functional.Functional (toClass a).
Proof.
  intros a. split; intros H1; assumption.
Qed.

(* Being functional is compatible with set inclusion (not quite of course).     *)
Proposition InclCompat : forall (a b:U),
  a :<=: b -> Functional b -> Functional a.
Proof.
  intros a b H1 H2 x y z H3 H4. apply (H2 x); apply H1; assumption.
Qed.

(* A functional set is functional at all points.                                *)
Proposition IsFunctionalAt : forall (a:U),
  Functional a <-> forall b, FunctionalAt a b.
Proof.
  intros a. split; intros H1.
  - intros b y z. apply H1.
  - intros x. apply H1.
Qed.
