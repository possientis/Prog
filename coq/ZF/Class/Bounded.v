Require Import ZF.Core.
Require Import ZF.Class.
Require Import ZF.Axiom.Specification.
Require Import ZF.Class.Small.

(* Predicate on classes, stating that a class is smaller than a set.            *)
Definition Bounded (P:Class) : Prop := exists a, forall x, P x -> x :< a.

(* A class is small if and only if it is bounded.                               *)
Proposition BoundedClassIsSmall : forall (P:Class),
  Bounded P <-> Small P.
Proof.
  (* Let P be an aribitrary class *)
  intros P. split.

  (* Proof of Bounded -> Small. So we assume that P is bounded *)
  - intros HBounded.

    (* There exists a set a such that P x -> x :< a for all x *)
    destruct HBounded as [a H1].

    (* so P x -> x :< a for all x *)
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
    + rewrite Hb in H2. apply SpecCharac in H2. destruct H2 as [_ H2]. apply H2.

    (* Proof of <- *)
    + rewrite Hb. apply SpecCharac. split.
      * apply H1, H2.
      * apply H2.

  (* Proof of Small -> Bounded. So we assume that P is small *)
  - intros HSmall.

    (* There exists a set a such that P x <-> x :< a for all x *)
    destruct HSmall as [a H1].

    (* We need to show the existence of a set b such that x :< b -> P x *)
    assert (exists b, forall x, P x -> x :< b) as A. 2: apply A.

    (* The set a itself has the desired property *)
    exists a.

    intros x H2. apply H1, H2.
Qed.
