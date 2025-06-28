Require Import ZF.Class.Core.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Image.


(* The range of a set.                                                          *)
Definition range (f:U) : U := fromClass (Range.range(toClass f))
  (Range.IsSmall (toClass f) (SetIsSmall f)).

(* The class of the range is the range of the class.                            *)
Proposition ToClass : forall (f:U),
  toClass (range f) :~: Class.Relation.Range.range (toClass f).
Proof.
  intros f. apply ToFromClass.
Qed.

Proposition Charac : forall (f y: U),
  y :< range f <-> exists x, :(x,y): :< f.
Proof.
  intros f y. split; intros H1.
  - apply FromClass.Charac in H1. destruct H1 as [x H1]. exists x. assumption.
  - destruct H1 as [x H1]. apply FromClass.Charac. exists x. assumption.
Qed.

(* The range is compatible with set inclusion.                                  *)
Proposition InclCompat : forall (f g:U),
  f :<=: g -> range f :<=: range g.
Proof.
  intros f g H1 y H2. apply Charac in H2. destruct H2 as [x H2].
  apply Charac. exists x. apply H1. assumption.
Qed.

Proposition ImageOfDomain : forall (f:U),
  f:[domain f]: = range f.
Proof.
  intros f. apply DoubleInclusion. split; intros y H1.
  - apply Image.Charac in H1. destruct H1 as [x [H1 H2]].
    apply Charac. exists x. assumption.
  - apply Charac in H1. destruct H1 as [x H1]. apply Image.Charac.
    exists x. split. 2: assumption. apply Domain.Charac. exists y. assumption.
Qed.

Proposition IsNotEmpty : forall (f:U),
  domain f <> :0: -> range f <> :0:.
Proof.
  intros f H1. apply Empty.HasElem in H1. destruct H1 as [x H1].
  apply Domain.Charac in H1. destruct H1 as [y H1].
  apply Empty.HasElem. exists y. apply Charac. exists x. assumption.
Qed.
