Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.FunctionalAt.

(* A functional set.                                                            *)
Definition Functional (a:U) : Prop :=
  forall x y z, :(x,y): :< a -> :(x,z): :< a -> y = z.

(* Being functional is compatible with set inclusion (not quite of course).     *)
Proposition InclCompat : forall (f g:U),
  f :<=: g -> Functional g -> Functional f.
Proof.
  intros f g H1 H2 x y z H3 H4. apply (H2 x); apply H1; assumption.
Qed.

(* A functional set is functional at all points.                                *)
Proposition IsFunctionalAt : forall (f:U),
  Functional f <-> forall a, FunctionalAt f a.
Proof.
  intros f. split; intros H1.
  - intros a y z. apply H1.
  - intros x. apply H1.
Qed.
