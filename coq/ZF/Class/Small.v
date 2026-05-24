Require Import ZF.Axiom.Replacement.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Set.Core.

(* Predicate on classes, stating that a class is actually a set.                *)
Definition Small (P:Class) : Prop := exists a, forall x, x :< a <-> P x.

(* The class associated with a set is small.                                    *)
Proposition SetIsSmall : forall (a:U), Small (toClass a).
Proof.
  intros a. exists a. intro x. unfold toClass. split; auto.
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

(* Axiom.Replacement is used directly here because Class.Relation.Replacement   *)
(* transitively imports Class.Small, which would be circular.                   *)
(* The property of being small is compatible with class inclusion.              *)
Proposition InclCompat : forall (A B:Class),
  A :<=: B -> Small B -> Small A.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)

  (* Let A and B be classes with A included in B, and let b witness Small B.    *)
  intros A B H1 [b H2].

  (* The binary predicate F(x,y) := (x = y) ∧ A(x) is functional.               *)
  assert (Replacement.Functional (fun x y => x = y /\ A x)) as H3. {
    intros x y z [H4 _] [H5 _]. rewrite <- H4, <- H5. reflexivity.
  }

  (* By replacement applied to F and b, there exists a set c with               *)
  (* y ∈ c ↔ ∃x, x ∈ b ∧ x = y ∧ A(x), which simplifies to y ∈ c ↔ A(y).        *)
  destruct (Replacement.Replacement _ H3 b) as [c H4].

  (* We claim c witnesses Small A.                                              *)
  exists c. intros x. split; intros H5.

  (* If x ∈ c, some w ∈ b satisfies w = x and A(w), so A(x).                    *)
  - apply H4 in H5. destruct H5 as [w [_ [H6 H7]]].
    rewrite <- H6. apply H7.

  (* If A(x), since A ⊆ B we have B(x), so x ∈ b. Taking y = x gives x ∈ c.     *)
  - apply H4. exists x. split.
    + apply H2, H1, H5.
    + split. 1: reflexivity. apply H5.
Qed.

