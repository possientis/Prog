Require Import ZF.Axiom.Replacement.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* Predicate on classes, stating that a class is actually a set.                *)
Definition Small (P:Class) : Prop := exists a, forall x, x :< a <-> P x.

(* The class associated with a set is small.                                    *)
Proposition SetIsSmall : forall (a:U), Small (toClass a).
Proof.
  intros a. exists a. intro x. split; auto.
Qed.

(* A class is small if and only if it is equivalent to some set.                *)
Proposition IsSomeSet : forall (P:Class),
  Small P <-> exists a, P :~: toClass a.
Proof.
  intros P. split; intros [a H1]; exists a.
  - apply Equiv.Sym. intros x. apply H1.
  - apply Equiv.Sym in H1. assumption.
Qed.

(* The property of being small is compatible with class equivalence.            *)
Proposition EquivCompat : forall (P Q:Class),
  P :~: Q -> Small P -> Small Q.
Proof.
  intros P Q H1 [a H2]. exists a. intros x. split; intros H3.
  - apply H1, H2, H3.
  - apply H2, H1, H3.
Qed.

(* The property of being small is compatible with class inclusion.              *)
Proposition InclCompat : forall (A B:Class),
  A :<=: B -> Small B -> Small A.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)

  (* Let A and B be classes with A included in B, and let b witness Small B.    *)
  intros A B H1 [b H2].

  (* The relation sending each x in A to itself is functional.                  *)
  assert (Functional (fun p => exists x, p = :(x,x): /\ A x)) as H3. {
    intros x y z H3 H4.
    destruct H3 as [x1 [H3 _]].
    destruct H4 as [x2 [H4 _]].
    apply OrdPair.Equal in H3. destruct H3 as [H3 H5].
    apply OrdPair.Equal in H4. destruct H4 as [H4 H6].
    subst. reflexivity.
  }

  (* By replacement, there is a set c containing exactly those elements of A.   *)
  destruct (Replacement _ H3 b) as [c H4].

  (* We claim c witnesses Small A.                                              *)
  exists c. intros x. split; intros H5.

  (* If x is in c, some w in b is related to x by the identity relation on A.   *)
  - apply H4 in H5. destruct H5 as [w [_ [u [H6 H7]]]].
    apply OrdPair.Equal in H6. destruct H6 as [H6 H8]. subst. assumption.

  (* If A(x), then A <= B gives B(x), so x is in b, hence x is in c.            *)
  - apply H4. exists x. split.
    + apply H2, H1, H5.
    + exists x. split. 2: assumption. reflexivity.
Qed.

