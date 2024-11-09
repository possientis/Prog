Require Import Logic.ZF.Class.
Require Import Logic.ZF.Core.
Require Import Logic.ZF.Specification.


Proposition BoundedClassIsSmall : forall (P:Class) (a:U),
  (forall x, P x -> x :< a) -> Small P.
Proof.
  (* Let P be a class bounded by a set a *)
  intros P a H1.

  (* i.e. such that P x -> x :< a for all x *)
  assert (forall x, P x -> x :< a) as A. { apply H1. } clear A.

  (* We need to show the existence of a set b such that x :< b <-> P x *)
  assert (exists b, forall x, x :< b <-> P x) as A. 2: apply A.

  (* Consider the set b = { x :< a | P x } *)
  remember :{a|P}: as b eqn:Hb.

  (* We claim that b has the desired property *)
  exists b.

  (* We need to show that x :< b <-> P x for all x*)
  assert (forall x, x :< b <-> P x) as A. 2: apply A.

  (* So let x be an arbitrary set *)
  intros x. split; intros H2.

  (* Proof of -> *)
  - rewrite Hb in H2. apply SpecCharac in H2. destruct H2 as [_ H2]. apply H2.

  (* Proof of <- *)
  - rewrite Hb. apply SpecCharac. split.
    + apply H1, H2.
    + apply H2.
Qed.

Proposition SmallIntersectSmall1 : forall (P Q:Class),
  Small P -> Small (fun x => P x /\ Q x).
Proof.
  intros P Q [a Ha]. apply BoundedClassIsSmall with a. intros x.
  intros [H1 _]. apply Ha, H1.
Qed.

Proposition SmallIntersectSmall2 : forall (P Q:Class),
  Small Q -> Small (fun x => P x /\ Q x).
Proof.
  intros P Q [a Ha]. apply BoundedClassIsSmall with a. intros x.
  intros [_ H1]. apply Ha, H1.
Qed.
