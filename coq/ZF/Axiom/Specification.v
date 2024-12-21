Require Import ZF.Axiom.Replacement.
Require Import ZF.Binary.
Require Import ZF.Binary.Functional.
Require Import ZF.Binary.Image.
Require Import ZF.Class.
Require Import ZF.Class.Small.
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

  (* We claim that this binary class is functional. *)
  assert (Functional F) as H2.
    { intros x y z H3 H4. rewrite H1 in H3. rewrite H1 in H4.
      destruct H3 as [_ H3]. destruct H4 as [_ H4]. subst.
      reflexivity.
    }

  (* We claim that the class F[a] (direct image of the set a by F) is the same  *)
  (* as the class fun x => x :< a /\ P x.                                       *)
  assert (forall x, F:[toClass a]: x <-> x :< a /\ P x) as H3.
    { rewrite H1. unfold image. intros x. split; intros H4.
      - destruct H4 as [y [H5 [H6 H7]]]. subst. auto.
      - exists x. split.
        + destruct H4 as [H4 _]. apply H4.
        + split. 2: reflexivity. destruct H4 as [_ H4]. apply H4.
    }

  (* We need to show the existence of b such that x :< b <-> x :< a /\ P x.*)
  assert (exists b, forall x, x :< b <-> x :< a /\ P x) as A. 2: apply A.

  (* Let us take b to be the direct image of a by the functional relation F     *)
  (* which is a small class and can be viewed as a set.                         *)
  exists (replaceSet F a H2).

  (* We need to show x :< b <-> x :< a /\ P x *)
  assert (forall x, x :< (replaceSet F a H2) <-> x :< a /\ P x) as A. 2: apply A.

  intros x. split.

  (* Proof of -> *)
  - assert (x :< (replaceSet F a H2) -> x :< a /\ P x) as A. 2: apply A.
    intros H4. apply ReplaceCharac, H3 in H4. apply H4.

  (* Proof of <- *)
  - assert (x :< a /\ P x -> x :< (replaceSet F a H2)) as A. 2: apply A.
    intros H4. apply ReplaceCharac, H3. apply H4.
Qed.
