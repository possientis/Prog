Require Import ZF.Class.Core.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.OrdPair.

(* This is a theorem and not an axiom as it can be derived from replacement.    *)
(* Given a class P and a set a, there exists a set b whose elements are the     *)
(* elements of the set a which are in P.                                        *)
Theorem Specification : forall (P:Class),
  forall a, exists b, forall x, x :< b <-> x :< a /\ P x.
Proof.
  (* Let P be a class and a be a set. *)
  intros P a.

  (* We need to show the existence of a set b with the desired property. *)
  assert (exists b, forall x, x :< b <-> x :< a /\ P x) as A. 2: apply A.

  (* Consider the class Q ={ x :< a | P x }. *)
  remember (fun x => x :< a /\ P x) as Q eqn:Eq.

  (* Let us assume that Q is small. *)
  assert (Small Q) as Hq. 2: {

  (* Then Q is actually a set b. *)
  remember (fromClass Q Hq) as b eqn:Eb.

  (* And we claim this set has the required property. *)
  exists b.

  (* Which is true *)
  intros x. rewrite Eb. split; intros H1.
  - apply FromClassCharac in H1. rewrite Eq in H1. assumption.
  - apply FromClassCharac. rewrite Eq. assumption.
  }

  (* So it remains to show that Q is small. *)
  assert (Small Q) as A. 2: apply A.

  (* Consider the class F (x,y) := P x /\ x = y. *)
  remember (fun u => exists x y, u = :(x,y): /\ P x /\ x = y) as F eqn:Ef.

  (* We claim that the direct image F[a] is Q *)
  assert (F:[toClass a]: :~: Q) as H2. {
    intros y. split; intros H3.
    - destruct H3 as [x [H3 H4]].
      rewrite Ef in H4. destruct H4 as [x' [y' [H4 [H5 H6]]]].
      apply OrdPairEqual in H4. destruct H4 as [H4 H7]. subst. split; assumption.
    - rewrite Eq in H3. destruct H3 as [H3 H4]. exists y. rewrite Ef.
      split. 1: assumption. exists y. exists y. split. 1: reflexivity.
      split. { assumption. } { reflexivity. }
  }

  (* Using this equivalence... *)
  apply SmallEquivCompat with F:[toClass a]:. 1: apply H2.

  (* It is sufficient to show that F[a] is small *)
  assert (Small F:[toClass a]:) as A. 2: apply A.

  (* Which we know is true since a set is small ... *)
  apply ImageIsSmall. 2: apply SetIsSmall.

  (* Provided we show that F is functional *)
  assert (Functional F) as A. 2: apply A.

  assert (Functional F) as Hf. {
    intros x y z H3 H4. rewrite Ef in H3. rewrite Ef in H4.
    destruct H3 as [x1 [y1 [H3 [H5 H6]]]]. destruct H4 as [x2 [y2 [H4 [H7 H8]]]].
    apply OrdPairEqual in H3. destruct H3 as [H3 H9].
    apply OrdPairEqual in H4. destruct H4 as [H4 H10].
    subst. reflexivity.
  }

  apply Hf.

Qed.
