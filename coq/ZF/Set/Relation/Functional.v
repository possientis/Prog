Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.FunctionalAt.

Module CRL := ZF.Class.Relation.Functional.

(* A functional set.                                                            *)
Definition Functional (f:U) : Prop :=
  forall x y z, :(x,y): :< f -> :(x,z): :< f -> y = z.

Proposition ToClass : forall (f:U),
  Functional f <-> CRL.Functional (toClass f).
Proof.
  intros f. split; intros H1 x y z H3 H4; apply H1 with x; assumption.
Qed.

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

