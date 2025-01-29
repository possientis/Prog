Require Import ZF.Class.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.Specify.

(* Predicate on classes, stating that a class is smaller than a set.            *)
Definition Bounded (P:Class) : Prop := exists a, forall x, P x -> x :< a.

Proposition LesserThanSmallIsSmall : forall (P Q:Class),
  P :<=: Q -> Small Q -> Small P.
Proof.

  (* Let P and Q be arbitrary classes. *)
  intros P Q.

  (* We assume that P <= Q. *)
  intros H1. assert (P :<=: Q) as A. { apply H1. } clear A.

  (* We assume that Q is small. *)
  intros H2. assert (Small Q) as A. { apply H2. } clear A.

  (* In particular Q is equivalent to some set a. *)
  assert (exists a, toClass a :~: Q) as H3. { apply (proj1 (SmallIsSomeSet _)), H2. }

  (* So let a be a set equivalent to the class Q. *)
  destruct H3 as [a H3].

  (* We need to show that P is small. *)
  assert (Small P) as A. 2: apply A.

  (* We have P x -> x :< a for all x. *)
  assert (forall x, P x -> x :< a) as H4. {
    intros x H. apply H3, H1, H.
  }

  (* We need to show the existence of a set b such that x :< b <-> P x. *)
  assert (exists b, forall x, x :< b <-> P x) as A. 2: apply A.

  (* Consider the set b = { x :< a | P x }. *)
  remember :{a|P}: as b eqn:Eb.

  (* We claim that b has the desired property. *)
  exists b.

  (* We need to show that x :< b <-> P x for all x. *)
  assert (forall x, x :< b <-> P x) as A. 2: apply A.

  (* So let x be an arbitrary set *)
  intros x. split; intros H5.

  (* Proof of -> *)
  - rewrite Eb in H5. apply SpecifyCharac in H5. destruct H5 as [_ H5]. apply H5.

  (* Proof of <- *)
  - rewrite Eb. apply SpecifyCharac. split.
    + apply H4. assumption.
    + assumption.
Qed.

(* A class is small if and only if it is bounded.                               *)
Proposition BoundedIsSmall : forall (P:Class),
  Bounded P <-> Small P.
Proof.
  intros P. split; intros H1; destruct H1 as [a H1].
  - apply LesserThanSmallIsSmall with (toClass a).
    intros x. apply H1. apply SetIsSmall.
  - exists a. intros x H2. apply H1. assumption.
Qed.
