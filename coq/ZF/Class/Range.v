Require Import ZF.Class.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Small.
Require Import ZF.Class.Snd.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* The range of a class.                                                        *)
Definition range (F:Class) : Class := fun y => exists x, F :(x,y):.

Proposition RangeEquivCompat : forall (F G:Class),
  F :~: G -> range F :~: range G.
Proof.
  intros F G H1 y. split; intros H2; destruct H2 as [x H2];
  exists x; apply H1; assumption.
Qed.

Proposition RangeInclCompat : forall (F G:Class),
  F :<=: G -> range F :<=: range G.
Proof.
  intros F G H1 y H2. destruct H2 as [x H2]. exists x. apply H1, H2.
Qed.

(* The direct image of a class P by Snd is the range of P.                      *)
Lemma ImageBySnd : forall (F:Class),
  Snd :[F]: :~: range F.
Proof.
  intros F x. split; intros H1.
  - unfold image in H1. destruct H1 as [x' [H1 H2]]. apply SndCharac2 in H2.
    destruct H2 as [y [z [H2 H3]]]. exists y.
    subst. assumption.
  - destruct H1 as [z H1]. unfold image. exists :(z,x):. split.
    + assumption.
    + apply SndCharac2. exists z. exists x. split; reflexivity.
Qed.

Proposition RangeIsSmall : forall (F:Class),
  Small F -> Small (range F).
Proof.
  (* Let F be an arbitrary class. *)
  intros F.

  (* We assume that F is small. *)
  intros H1. assert (Small F) as A. { apply H1. } clear A.

  (* We need to show that range(F) is small. *)
  assert (Small (range F)) as A. 2: apply A.

  (* Using the equivalence Snd[F] ~ range(F) ... *)
  apply SmallEquivCompat with Snd:[F]:. 1: apply ImageBySnd.

  (* It is sufficient to show that Snd[F] is small. *)
  assert (Small (Snd:[F]:)) as A. 2: apply A.

  (* This follows from the fact that Snd is functional and F is small. *)
  apply FunctionalImageIsSmall.

  - apply SndIsFunctional.

  - apply H1.
Qed.

Proposition RangeIsDomainImage : forall (F:Class),
  F:[domain F]: :~: range F.
Proof.
  intros F y. split; intros H1.
  - destruct H1 as [x [H1 H2]]. exists x. assumption.
  - destruct H1 as [x H1]. exists x. split. 2: assumption. exists y. assumption.
Qed.

