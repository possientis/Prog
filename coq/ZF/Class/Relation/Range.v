Require Import ZF.Class.Equiv.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Small.
Require Import ZF.Class.Relation.Snd.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* The range of a class.                                                        *)
Definition range (F:Class) : Class := fun y => exists x, F :(x,y):.

Proposition EquivCompat : forall (F G:Class),
  F :~: G -> range F :~: range G.
Proof.
  intros F G H1 y. split; intros H2; destruct H2 as [x H2];
  exists x; apply H1; assumption.
Qed.

Proposition InclCompat : forall (F G:Class),
  F :<=: G -> range F :<=: range G.
Proof.
  intros F G H1 y H2. destruct H2 as [x H2]. exists x. apply H1, H2.
Qed.

(* The direct image of a class P by Snd is the range of P.                      *)
Lemma ImageBySnd : forall (F:Class),
  Snd :[F]: :~: range F.
Proof.
  intros F x. split; intros H1.
  - unfold image in H1. destruct H1 as [x' [H1 H2]]. apply Snd.Charac2 in H2.
    destruct H2 as [y [z [H2 H3]]]. exists y.
    subst. assumption.
  - destruct H1 as [z H1]. unfold image. exists :(z,x):. split.
    + assumption.
    + apply Snd.Charac2. exists z. exists x. split; reflexivity.
Qed.

Proposition IsSmall : forall (F:Class),
  Small F -> Small (range F).
Proof.
  (* Let F be an arbitrary class. *)
  intros F.

  (* We assume that F is small. *)
  intros H1. assert (Small F) as A. { apply H1. } clear A.

  (* We need to show that range(F) is small. *)
  assert (Small (range F)) as A. 2: apply A.

  (* Using the equivalence Snd[F] ~ range(F) ... *)
  apply Small.EquivCompat with Snd:[F]:. 1: apply ImageBySnd.

  (* It is sufficient to show that Snd[F] is small. *)
  assert (Small (Snd:[F]:)) as A. 2: apply A.

  (* This follows from the fact that Snd is functional and F is small. *)
  apply Image.IsSmall.

  - apply Snd.IsFunctional.

  - apply H1.
Qed.

Proposition ImageOfDomain : forall (F:Class),
  F:[domain F]: :~: range F.
Proof.
  intros F y. split; intros H1.
  - destruct H1 as [x [H1 H2]]. exists x. assumption.
  - destruct H1 as [x H1]. exists x. split. 2: assumption. exists y. assumption.
Qed.

(* If the domain of F is not empty, then neither is the range.                  *)
Proposition IsNotEmpty : forall (F:Class),
  domain F :<>: :0: -> range F :<>: :0:.
Proof.
  intros F H1. apply Empty.HasElem in H1. destruct H1 as [x [y H1]].
  apply Empty.HasElem. exists y. exists x. assumption.
Qed.

Proposition ImageIsIncl : forall (F A:Class),
  F:[A]: :<=: range F.
Proof.
  intros F A y H1. destruct H1 as [x [H1 H2]]. exists x. assumption.
Qed.
