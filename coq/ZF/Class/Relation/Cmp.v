Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* Cmp is the class of ordered pairs of the form (((x,y),(y',z)),(x,z)).        *)
(* This class is useful to prove that composition of two small classes is small.*)
Definition Cmp : Class := fun u =>
  exists x y y' z, u = :(:(:(x,y):,:(y',z):):,:(x,z):):.

Proposition Charac2 : forall (u v:U),
  Cmp :(u,v): <-> exists x y y' z, u = :(:(x,y):,:(y',z):): /\ v = :(x,z):.
Proof.
  intros u v. split; intros H1.
  - destruct H1 as [x [y [y' [z H1]]]]. apply OrdPair.WhenEqual in H1.
    exists x. exists y. exists y'. exists z. assumption.
  - destruct H1 as [x [y [y' [z [H1 H2]]]]].
    exists x. exists y. exists y'. exists z. rewrite H1, H2. reflexivity.
Qed.

Proposition IsFunctional : Functional Cmp.
Proof.
  intros u v v' H1 H2. apply Charac2 in H1. apply Charac2 in H2.
  destruct H1 as [x1 [y1 [y1' [z1 [H1 H3]]]]].
  destruct H2 as [x2 [y2 [y2' [z2 [H2 H4]]]]].
  subst. apply OrdPair.WhenEqual in H2. destruct H2 as [H1 H2].
  apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3].
  apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H4].
  subst. reflexivity.
Qed.
