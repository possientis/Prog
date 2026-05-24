Require Import ZF.Class.Equiv.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.Snd.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* The range of a class.                                                        *)
Definition range (F:Class) : Class := fun y => exists x, F :(x,y):.

(* The range is compatible with class equivalence.                              *)
Proposition EquivCompat : forall (F G:Class),
  F :~: G -> range F :~: range G.
Proof.
  intros F G H1 y. split; intros H2; destruct H2 as [x H2];
  exists x; apply H1; assumption.
Qed.

(* The range is compatible with class inclusion.                                *)
Proposition InclCompat : forall (F G:Class),
  F :<=: G -> range F :<=: range G.
Proof.
  intros F G H1 y H2. destruct H2 as [x H2]. exists x. apply H1, H2.
Qed.

(* The direct image of a class F under Snd is the range of F.                   *)
Proposition ImageUnderSnd : forall (F:Class),
  Snd :[F]: :~: range F.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros F y. split; intros H1.
  - (* A Snd-image of a pair in F is the second coordinate of that pair.        *)
    destruct H1 as [x' [H1 H2]]. apply Snd.Charac2 in H2.
    destruct H2 as [x [z [H2 H3]]]. exists x. subst. assumption.
  - (* Conversely, every second coordinate of a pair in F is in the Snd-image.  *)
    destruct H1 as [x H1]. exists :(x,y):. split. 1: assumption.
    apply Snd.Charac2. exists x. exists y. split; reflexivity.
Qed.

(* The direct image of the domain of a class F under F is the range of F.       *)
Proposition ImageOfDomain : forall (F:Class),
  F:[domain F]: :~: range F.
Proof.
  intros F y. split; intros H1.
  - destruct H1 as [x [H1 H2]]. exists x. assumption.
  - destruct H1 as [x H1]. exists x. split. 2: assumption. exists y. assumption.
Qed.

(* The range of a small class is a small class.                                 *)
Proposition IsSmall : forall (F:Class),
  Small F -> Small (range F).
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* Let F be an arbitrary class.                                               *)
  intros F.

  (* We assume that F is small.                                                 *)
  intros H1. assert (Small F) as A. { apply H1. } clear A.

  (* We need to show that range(F) is small.                                    *)
  assert (Small (range F)) as A. 2: apply A.

  (* Using the equivalence F[domain F] ~ range(F) ...                           *)
  apply Small.EquivCompat with F:[domain F]:. 1: apply ImageOfDomain.

  (* Since F is small, so is F[domain F].                                       *)
  apply Image.IsSmallL. apply H1.
Qed.

(* If the domain of F is not empty, then neither is the range.                  *)
Proposition IsNotEmpty : forall (F:Class),
  domain F :<>: :0: -> range F :<>: :0:.
Proof.
  intros F H1. apply Empty.HasElem in H1. destruct H1 as [x [y H1]].
  apply Empty.HasElem. exists y. exists x. assumption.
Qed.

(* The direct image of a class under F is a subclass of the range of F.         *)
Proposition ImageIsIncl : forall (F A:Class),
  F:[A]: :<=: range F.
Proof.
  intros F A y H1. destruct H1 as [x [H1 H2]]. exists x. assumption.
Qed.
