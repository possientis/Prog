Require Import ZF.Axiom.Replacement.
Require Import ZF.Binary.
Require Import ZF.Binary.Functional.
Require Import ZF.Binary.Image.
Require Import ZF.Class.
Require Import ZF.Class.Small.
Require Import ZF.Core.Image.
Require Import ZF.Set.
Require Import ZF.Set.Replace.

(* Given a set theoretic predicate P and a set a, there exists a set b whose    *)
(* elements are the elements of the set a which satisfy P.                      *)
(* This is a theorem and not an axiom as it can be derived from replacement.    *)
Theorem Specification : forall (P:U -> Prop),
  forall a, exists b, forall x, x :< b <-> x :< a /\ P x.
Proof.
  (* Let P be a predicate and a be a set. *)
  intros P a.

  (* Consider the binary class F x y := P x /\ x = y. *)
  remember (fun x y => P x /\ x = y) as F eqn:H1.

  (* Consider the class A associated with the set a. *)
  remember (toClass a) as A eqn:Ea.

  (* Note that the class A is small. *)
  assert (Small A) as Ha. { rewrite Ea. apply SetIsSmall. }

  (* We claim the binary class F is functional. *)
  assert (Functional F) as Hf.
    { intros x y z H3 H4. rewrite H1 in H3. rewrite H1 in H4.
      destruct H3 as [_ H3]. destruct H4 as [_ H4]. subst.
      reflexivity.
    }

  (* We claim the class F[A] is the same as fun x => x :< a /\ P x. *)
  assert (forall x, F:[A]: x <-> x :< a /\ P x) as H3.
    { rewrite H1. unfold image. intros x. split; intros H4.
      - destruct H4 as [y [H5 [H6 H7]]]. subst. auto.
      - exists x. split.
        + rewrite Ea. destruct H4 as [H4 _]. apply H4.
        + split. 2: reflexivity. destruct H4 as [_ H4]. apply H4.
    }

  (* We need to show the existence of b such that x :< b <-> x :< a /\ P x.*)
  assert (exists b, forall x, x :< b <-> x :< a /\ P x) as A'. 2: apply A'.

  (* Let us take b = { F x | A x }. Such a set exists since F is functional and *)
  (* the class A is small.                                                      *)
  remember (replaceSet F A Hf Ha) as b eqn:Eb.

  (* We claim that b has the desired property. *)
  exists b.

  (* We need to show x :< b <-> x :< a /\ P x *)
  assert (forall x, x :< b <-> x :< a /\ P x) as A'. 2: apply A'.

  intros x. split.

  (* Proof of -> *)
  - assert (x :< b -> x :< a /\ P x) as A'. 2: apply A'.
    intros H4. rewrite Eb in H4.
    apply ReplaceCharac in H4. apply H3, H4.

  (* Proof of <- *)
  - assert (x :< a /\ P x -> x :< b) as A'. 2: apply A'.
    intros H4. rewrite Eb.
    apply ReplaceCharac. apply H3, H4.
Qed.

