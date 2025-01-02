Require Import ZF.Binary.Domain.
Require Import ZF.Class.
Require Import ZF.Class.FromBinary.
Require Import ZF.Class.Fst.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Small.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Image.
Require Import ZF.Core.Leq.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* The domain of a class is the domain of its binary class.                     *)
Definition domain (P:Class) : Class := Domain.domain (toBinary P).

(* Quick unfolding.                                                             *)
Proposition DomainCharac : forall (P:Class) (x:U),
  domain P x <-> exists y, P :(x,y):.
Proof.
  intros P x. split; intros H1; assumption.
Qed.

Proposition DomainEquivCompat : forall (P Q:Class),
  P :~: Q -> domain P :~: domain Q.
Proof.
  intros P Q H1 x. split; intros H2;
  apply (proj1 (DomainCharac _ _)) in H2; destruct H2 as [y H2];
  apply DomainCharac; exists y.
  - apply H1. assumption.
  - apply ClassEquivSym in H1. apply H1. assumption.
Qed.

Proposition DomainInclCompat : forall (P Q:Class),
  P :<=: Q -> domain P :<=: domain Q.
Proof.
  intros P Q H1 x H2. apply (proj1 (DomainCharac P x)) in H2. destruct H2 as [y H2].
  apply DomainCharac. exists y. apply H1, H2.
Qed.

(* The direct image of a class P by Fst is the domain of P.                     *)
Lemma ImageByFst : forall (P:Class),
  Fst :[P]: :~: domain P.
Proof.
  intros P x. split; intros H1.
  - unfold image in H1. destruct H1 as [x' [H1 H2]]. apply FstCharac2 in H2.
    destruct H2 as [y [z [H2 H3]]]. apply DomainCharac. exists z.
    subst. assumption.
  - apply (proj1 (DomainCharac _ _)) in H1. destruct H1 as [y H1].
    unfold image. exists :(x,y):. split.
    + assumption.
    + apply FstCharac2. exists x. exists y. split; reflexivity.
Qed.

Proposition DomainIsSmall : forall (P:Class),
  Small P -> Small (domain P).
Proof.
  (* Let P be an arbitrary class. *)
  intros P.

  (* We assume that P is small. *)
  intros H1. assert (Small P) as A. { apply H1. } clear A.

  (* We need to show that domain(P) is small. *)
  assert (Small (domain P)) as A. 2: apply A.

  (* Using the equivalence Fst[P] ~ domain(P) ... *)
  apply SmallEquivCompat with Fst:[P]:. 1: apply ImageByFst.

  (* It is sufficient to show that Fst[P] is small. *)
  assert (Small (Fst:[P]:)) as A. 2: apply A.

  (* This follows from the fact that Fst is functional and P is small. *)
  apply ImageIsSmall.

  - apply FstIsFunctional.

  - apply H1.
Qed.
