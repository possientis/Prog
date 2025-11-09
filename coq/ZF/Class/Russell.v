Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.
Require Import ZF.Class.Proper.
Require Import ZF.Set.Core.
Require Import ZF.Set.Specify.

(* Let us the define the class of all sets which do not belong to themselves.   *)
Definition Ru : Class := fun x => ~x :< x.

(* Then this is a proper class                                                  *)
Proposition ProperRu : Proper Ru.
Proof.
  unfold Proper, Small, Ru.

  (* We need to show there is no set a with x :< a <-> ~ x :< x *)
  assert (~ exists a, forall x, x :< a <-> ~ x :< x ) as A. 2: apply A.

  (* We assume that such a set exists and need to obtain a contradiction  *)
  intros [a Ha].

  (* We claim that the set a is not an element of itself *)
  assert (~ a :< a) as H1. {

    (* Assume that a is an element of itself *)
    intros H2.

    (* Then from the assumption we have ~ a :< a which is a contradiction *)
    apply (Ha a); apply H2.
  }

  (* To arrive at a contradiction it is sufficient to prove that a :< a *)
  apply H1.

  (* So we need to prove that a is an element of itself *)
  assert (a :< a) as A. 2: apply A.

  (* By assumption this is equivalent to proving ~ a :< a *)
  apply Ha.

  (* Which we have already done *)
  apply H1.
Qed.

(* There exists no set containing all sets                                      *)
Proposition Russell : ~ exists a, forall x, x :< a.
Proof.
  (* Let a be a set containing all sets *)
  intros [a Ha].

  (* We arrive at a contradiction by showing the class Ru is small *)
  apply ProperRu.

  (* So we need to show that Ru is a small class *)
  assert (Small Ru) as A. 2: apply A. unfold Small.

  (* i.e. We need to show the existence of b such that x :< b <-> Ru x *)
  assert (exists b, forall x, x :< b <-> Ru x) as A. 2: apply A.

  (* Consider the set b = {x :< a | Ru x } *)
  remember :{a|Ru}: as b eqn:Eb.

  (* We claim that b has the desired property *)
  exists b.

  (* We need to show the equivalence x :< b <-> Ru x for all x *)
  assert (forall x, x :< b <-> Ru x) as A. 2: apply A.

  (* So let x be an arbitary set *)
  intros x. split.

  (* Proof of -> *)
  - assert (x :< b -> Ru x) as A. 2: apply A.
    intros H1. rewrite Eb in H1. apply Specify.IsInP with a. apply H1.

  (* Proof of <- *)
  - assert (Ru x -> x :< b) as A. 2: apply A.
    intros H1. rewrite Eb. apply Specify.Charac. split.
    + apply Ha.
    + apply H1.
Qed.

