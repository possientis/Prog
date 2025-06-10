Require Import ZF.Class.Bounded.
Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Small.
Require Import ZF.Class.Union2.
Require Import ZF.Set.OrdPair.

(* A relation class is a class whose elements are ordered pairs.                *)
Definition Relation (F:Class) : Prop :=
    forall x, F x -> exists y, exists z, x = :(y,z):.

(* The pairwise union of two relation classes is a relation class.              *)
Proposition Union2 : forall (F G:Class),
  Relation F -> Relation G -> Relation (F:\/:G).
Proof.
  intros F G Hp Hq x H1. destruct H1 as [H1|H1].
  - apply Hp, H1.
  - apply Hq, H1.
Qed.

(* A function is a subclass of the product of its domain and image thereof.     *)
Proposition IsIncl : forall (F:Class),
  Relation F -> F :<=: (domain F) :x: F:[domain F]:.
Proof.
  intros F H1 x H3. unfold Relation in H1. specialize (H1 x H3).
  destruct H1 as [y [z H1]]. exists y. exists z. split. 1: assumption. split.
  - exists z. subst. assumption.
  - exists y. split.
    + exists z. subst. assumption.
    + subst. assumption.
Qed.

(* A functional relation with a small domain is small.                          *)
Proposition IsSmall : forall (F:Class),
  Relation F -> Functional F -> Small (domain F) -> Small F.
Proof.

  (* Let F be an arbitrary class. *)
  intros F.

  (* We assume that F is a relation. *)
  intros H1. assert (Relation F) as X. { apply H1. } clear X.

  (* We assume that F is functional. *)
  intros H2. assert (Functional F) as X. { apply H2. } clear X.

  (* We assume that F has a small domain. *)
  intros H3. assert (Small (domain F)) as X. { apply H3. } clear X.

  (* We need to show that F is small. *)
  assert (Small F) as X. 2: apply X.

  (* Being a relation we have F <= (domain F) x F[domain F]. *)
  apply IsIncl in H1.
  assert (F :<=: domain F :x: F:[domain F]: ) as X. { apply H1. } clear X.

  (* Thus, in order to prove that F is small ... *)
  apply InclInSmallIsSmall with (domain F :x: F:[domain F]:). 1: apply H1.

  (* It is sufficient to prove that (domain F) x F[domain F] is small *)
  assert (Small (domain F :x: F:[domain F]:)) as X. 2: apply X.

  (* To show that this product class is small ... *)
  apply Prod.IsSmall.

  (* We need to argue that domain F is small, which is true by assumption. *)
  - assert (Small (domain F)) as X. 2: apply X. assumption.

  (* And we need to show that F[domain F] is small. *)
  - assert (Small F:[domain F]:) as X. 2: apply X.

  (* Which follows from the fact that F is functional and domain F is small. *)
    apply Image.IsSmall. { apply H2. } { apply H3. }
Qed.
