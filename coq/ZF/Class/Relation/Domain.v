Require Import ZF.Class.Core.
Require Import ZF.Class.Relation.Fst.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* The domain of a class.                                                       *)
Definition domain (F:Class) : Class := fun x => exists y, F :(x,y):.

(* The domain is compatible with class equivalence.                             *)
Proposition DomainEquivCompat : forall (F G:Class),
  F :~: G -> domain F :~: domain G.
Proof.
  intros F G H1 x. split; intros H2; destruct H2 as [y H2];
  exists y; apply H1; assumption.
Qed.

(* The domain is compatible with class inclusion.                               *)
Proposition DomainInclCompat : forall (F G:Class),
  F :<=: G -> domain F :<=: domain G.
Proof.
  intros F G H1 x H2. destruct H2 as [y H2]. exists y. apply H1, H2.
Qed.

(* The direct image of a class F by Fst is the domain of F.                     *)
Lemma ImageByFst : forall (F:Class),
  Fst :[F]: :~: domain F.
Proof.
  intros F x. split; intros H1.
  - destruct H1 as [x' [H1 H2]]. apply FstCharac2 in H2.
    destruct H2 as [y [z [H2 H3]]]. exists z. subst. assumption.
  - destruct H1 as [y H1]. exists :(x,y):. split.
    + assumption.
    + apply FstCharac2. exists x. exists y. split; reflexivity.
Qed.

(* The domain of a small class is a small class.                                *)
Proposition DomainIsSmall : forall (F:Class),
  Small F -> Small (domain F).
Proof.
  (* Let F be an arbitrary class. *)
  intros F.

  (* We assume that F is small. *)
  intros H1. assert (Small F) as A. { apply H1. } clear A.

  (* We need to show that domain(F) is small. *)
  assert (Small (domain F)) as A. 2: apply A.

  (* Using the equivalence Fst[F] ~ domain(F) ... *)
  apply Small.EquivCompat with Fst:[F]:. 1: apply ImageByFst.

  (* It is sufficient to show that Fst[F] is small. *)
  assert (Small (Fst:[F]:)) as A. 2: apply A.

  (* This follows from the fact that Fst is functional and F is small. *)
  apply Image.IsSmall.

  - apply FstIsFunctional.

  - apply H1.
Qed.

