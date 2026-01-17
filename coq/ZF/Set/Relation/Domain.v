Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Single.

Module CRD := ZF.Class.Relation.Domain.

(* The domain of a set.                                                         *)
Definition domain (f:U) : U := fromClass (CRD.domain (toClass f))
  (CRD.IsSmall (toClass f) (SetIsSmall f)).

(* The class of the domain is the domain of the class.                          *)
Proposition ToClass : forall (f:U),
  toClass (domain f) :~: CRD.domain (toClass f).
Proof.
  intros f. apply ToFromClass.
Qed.

Proposition Charac : forall (f x: U),
  x :< domain f <-> exists y, :(x,y): :< f.
Proof.
  intros f x. split; intros H1.
  - apply FromClass.Charac in H1. destruct H1 as [y H1]. exists y. assumption.
  - destruct H1 as [y H1]. apply FromClass.Charac. exists y. assumption.
Qed.

(* The domain is compatible with set inclusion.                                 *)
Proposition InclCompat : forall (f g:U),
  f :<=: g -> domain f :<=: domain g.
Proof.
  intros f g H1 x H2. apply Charac in H2. destruct H2 as [y H2].
  apply Charac. exists y. apply H1. assumption.
Qed.

Proposition WhenEmpty : forall (f:U),
  f = :0: -> domain f = :0:.
Proof.
  intros F H1. apply DoubleInclusion. split; intros x H2.
  - apply Charac in H2. destruct H2 as [y H2]. rewrite H1 in H2.
    apply Empty.Charac in H2. contradiction.
  - apply Empty.Charac in H2. contradiction.
Qed.

Proposition WhenSingle : forall (x y f:U),
  f = :{ :(x,y): }: -> domain f = :{x}:.
Proof.
  intros x y f H1. apply DoubleInclusion. split; intros u H2.
  - apply Charac in H2. destruct H2 as [v H2]. subst.
    apply Single.Charac in H2.
    apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H3]. subst.
    apply Single.Charac. reflexivity.
  - apply Single.Charac in H2. subst.
    apply Charac. exists y. apply Single.Charac. reflexivity.
Qed.

