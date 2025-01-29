Require Import ZF.Binary.Range.
Require Import ZF.Class.
Require Import ZF.Class.FromBinary.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Small.
Require Import ZF.Class.Snd.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* The range of a class is the range of its binary class.                       *)
Definition range (P:Class) : Class := Range.range (toBinary P).

(* Quick unfolding.                                                             *)
Proposition RangeCharac : forall (P:Class) (y:U),
  range P y <-> exists x, P :(x,y):.
Proof.
  intros P y. split; intros H1.
  - apply H1.
  - apply H1.
Qed.

Proposition RangeEquivCompat : forall (P Q:Class),
  P :~: Q -> range P :~: range Q.
Proof.
  intros P Q H1 y. split; intros H2;
  apply (proj1 (RangeCharac _ _)) in H2; destruct H2 as [x H2];
  apply RangeCharac; exists x; apply H1; assumption.
Qed.

Proposition RangeInclCompat : forall (P Q:Class),
  P :<=: Q -> range P :<=: range Q.
Proof.
  intros P Q H1 y H2. apply (proj1 (RangeCharac P y)) in H2. destruct H2 as [x H2].
  apply RangeCharac. exists x. apply H1, H2.
Qed.

(* The direct image of a class P by Snd is the range of P.                      *)
Lemma ImageBySnd : forall (P:Class),
  Snd :[P]: :~: range P.
Proof.
  intros P x. split; intros H1.
  - unfold image in H1. destruct H1 as [x' [H1 H2]]. apply SndCharac2 in H2.
    destruct H2 as [y [z [H2 H3]]]. apply RangeCharac. exists y.
    subst. assumption.
  - apply (proj1 (RangeCharac _ _)) in H1. destruct H1 as [z H1].
    unfold image. exists :(z,x):. split.
    + assumption.
    + apply SndCharac2. exists z. exists x. split; reflexivity.
Qed.

Proposition RangeIsSmall : forall (P:Class),
  Small P -> Small (range P).
Proof.
  (* Let P be an arbitrary class. *)
  intros P.

  (* We assume that P is small. *)
  intros H1. assert (Small P) as A. { apply H1. } clear A.

  (* We need to show that range(P) is small. *)
  assert (Small (range P)) as A. 2: apply A.

  (* Using the equivalence Snd[P] ~ range(P) ... *)
  apply SmallEquivCompat with Snd:[P]:. 1: apply ImageBySnd.

  (* It is sufficient to show that Snd[P] is small. *)
  assert (Small (Snd:[P]:)) as A. 2: apply A.

  (* This follows from the fact that Snd is functional and P is small. *)
  apply ImageIsSmall.

  - apply SndIsFunctional.

  - apply H1.
Qed.
