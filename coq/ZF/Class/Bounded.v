Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Specify.

(* Predicate on classes, stating that a class is smaller than a set.            *)
Definition Bounded (A:Class) : Prop := exists a, forall x, A x -> x :< a.

Proposition WhenSmaller : forall (A B:Class),
  A :<=: B -> Small B -> Small A.
Proof.

  (* Let A and B be arbitrary classes. *)
  intros A B.

  (* We assume that A <= B. *)
  intros H1. assert (A :<=: B) as X. { apply H1. } clear X.

  (* We assume that B is small. *)
  intros H2. assert (Small B) as X. { apply H2. } clear X.

  (* In particular B is equivalent to some set a. *)
  assert (exists a, B :~: toClass a) as H3. { apply Small.IsSomeSet, H2. }

  (* So let a be a set equivalent to the class B. *)
  destruct H3 as [a H3].

  (* We need to show that A is small. *)
  assert (Small A) as X. 2: apply X.

  (* We have A x -> x :< a for all x. *)
  assert (forall x, A x -> x :< a) as H4. {
    intros x H. apply H3, H1, H.
  }

  (* We need to show the existence of a set b such that x :< b <-> A x. *)
  assert (exists b, forall x, x :< b <-> A x) as X. 2: apply X.

  (* Consider the set b = { x :< a | P x }. *)
  remember :{a|A}: as b eqn:Eb.

  (* We claim that b has the desired property. *)
  exists b.

  (* We need to show that x :< b <-> A x for all x. *)
  assert (forall x, x :< b <-> A x) as X. 2: apply X.

  (* So let x be an arbitrary set *)
  intros x. split; intros H5.

  (* Proof of -> *)
  - rewrite Eb in H5. apply Specify.Charac in H5. destruct H5 as [_ H5]. apply H5.

  (* Proof of <- *)
  - rewrite Eb. apply Specify.Charac. split.
    + apply H4. assumption.
    + assumption.
Qed.

(* A class is small if and only if it is bounded.                               *)
Proposition IsSmall : forall (A:Class),
  Bounded A <-> Small A.
Proof.
  intros A. split; intros H1; destruct H1 as [a H1].
  - apply WhenSmaller with (toClass a).
    intros x. apply H1. apply SetIsSmall.
  - exists a. intros x H2. apply H1. assumption.
Qed.
