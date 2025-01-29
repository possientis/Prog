Require Import ZF.Binary.Functional.
Require Import ZF.Binary.Image.
Require Import ZF.Class.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.

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

  (* Consider the binary class F x y := P x /\ x = y. *)
  remember (fun x y => P x /\ x = y) as F eqn:Ef.

  (* We claim that the direct image F[a] is Q *)
  assert (F:[toClass a]: :~: Q) as H2. {
    intros y. split; intros H3.
    - apply (proj1 (ImageCharac _ _ _)) in H3. destruct H3 as [x [H3 H4]].
      rewrite Ef in H4. destruct H4 as [H4 H5]. subst. split; assumption.
    - rewrite Eq in H3. destruct H3 as [H3 H4]. apply ImageCharac.
      exists y. rewrite Ef. split.
      + assumption.
      + split. { assumption. } { reflexivity. }
  }

  (* Using this equivalence... *)
  apply SmallEquivCompat with F:[toClass a]:. 1: apply H2.

  (* It is sufficient to show that F[a] is small *)
  assert (Small F:[toClass a]:) as A. 2: apply A.

  (* Which we know is true since a set is small ... *)
  apply ImageIsSmall. 2: apply SetIsSmall.

  (* Provided we show that F is functional *)
  assert (Functional F) as A. 2: apply A.

  assert (Functional F) as Hf.
    { intros x y z H3 H4. rewrite Ef in H3. rewrite Ef in H4.
      destruct H3 as [_ H3]. destruct H4 as [_ H4]. subst.
      reflexivity.
    }

  apply Hf.
Qed.
