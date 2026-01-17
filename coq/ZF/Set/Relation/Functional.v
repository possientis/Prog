Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.FunctionalAt.
Require Import ZF.Set.Single.

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

Proposition WhenEmpty : forall (f:U),
  f = :0: -> Functional f.
Proof.
  intros f H1 x y1 y2 H2 H3. exfalso. subst.
  apply Empty.Charac in H2. contradiction.
Qed.

Proposition WhenSingle : forall (x y f:U),
  f = :{ :(x,y): }: -> Functional f.
Proof.
  intros x y f H1 u y1 y2 H2 H3. subst.
  apply Single.Charac in H2. apply Single.Charac in H3.
  apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H4].
  apply OrdPair.WhenEqual in H3. destruct H3 as [H3 H5].
  subst. reflexivity.
Qed.
