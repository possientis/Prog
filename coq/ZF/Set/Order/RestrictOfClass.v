Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Restrict.
Require Import ZF.Class.Prod.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Specify.

Export ZF.Notation.Slash.

Module CPR := ZF.Class.Prod.

(* The restriction of a class (viewed as relation) to a set.                    *)
Definition restrict (R:Class) (a:U) : U := {{ x :< a :x: a | R }}.

(* Notation "R :/: a" := (restrict R a)                                         *)
Global Instance ClassSetSlash : Slash Class U := { slash := restrict }.

Proposition Charac : forall (R:Class) (a x:U),
  x :< R:/:a <-> exists y z, x = :(y,z): /\ y :< a /\ z :< a /\ R :(y,z):.
Proof.
  intros R a x. split; intros H1.
  - apply Specify.Charac in H1. destruct H1 as [H1 H2].
    apply Prod.Charac in H1. destruct H1 as [y [z [H1 [H3 H4]]]]. subst.
    exists y. exists z. split. 1: reflexivity.
    split. 1: assumption. split; assumption.
  - destruct H1 as [y [z [H1 [H2 [H3 H4]]]]]. subst. apply Specify.Charac.
    split. 2: assumption. apply Prod.Charac2. split; assumption.
Qed.

Proposition Charac2 : forall (R:Class) (a y z:U),
  :(y,z): :< R:/:a <-> y :< a /\ z :< a /\ R :(y,z):.
Proof.
  intros R a y z. split; intros H1.
  - apply Charac in H1. destruct H1 as [y' [z' [H1 [H2 [H3 H4]]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H5]. subst.
    split. 1: assumption. split; assumption.
  - apply Charac. exists y. exists z. split. 1: reflexivity. assumption.
Qed.

Proposition ToClass : forall (R:Class) (a:U),
  toClass (R:/:a) :~: R :/: (toClass a).
Proof.
  intros R a x. split; intros H1.
  - apply Charac in H1. destruct H1 as [y [z [H1 [H2 [H3 H4]]]]]. subst.
    split. 1: assumption. apply CPR.Charac2. split; assumption.
  - destruct H1 as [H1 [y [z [H2 [H3 H4]]]]]. subst. apply Charac2.
    split. 1: assumption. split; assumption.
Qed.

Proposition IsRelation : forall (R:Class) (a:U), Relation (R:/:a).
Proof.
  intros R a x H1. apply Charac in H1. destruct H1 as [y [z [H1 _]]].
  exists y. exists z. assumption.
Qed.

Proposition InclR : forall (R:Class) (a x:U), x :< R:/:a -> R x.
Proof.
  intros R a x H1.
  apply Charac in H1. destruct H1 as [y [z [H1 [H2 [H3 H4]]]]].
  subst. assumption.
Qed.

Proposition InAL : forall (R:Class) (a x y:U),
  :(x,y): :< R:/:a -> x :< a.
Proof.
  intros R a x y H1. apply Charac2 in H1. apply H1.
Qed.

Proposition InAR : forall (R:Class) (a x y:U),
  :(x,y): :< R:/:a -> y :< a.
Proof.
  intros R a x y H1. apply Charac2 in H1. apply H1.
Qed.

