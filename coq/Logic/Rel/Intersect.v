Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R.
Require Import Logic.Rel.Converse.

(* Intersection operator. Needed for Rel to be an allegory.                     *) 
Definition inter (a b:Type) (r s:R a b) : R a b := fun x y => r x y /\ s x y.
Arguments inter {a} {b}.

Notation "r ^ s" := (inter r s)
    (at level 30, right associativity) : Rel_Intersect_scope.

Open Scope Rel_Intersect_scope.

(* Intersection is idempotent.                                                  *)
Lemma inter_idem : forall (a b:Type) (r:R a b), r ^ r = r.
Proof.
    intros a b r. apply Ext. intros x y. unfold inter. split.
    - intros [H1 H2]. assumption.
    - intros H1. split; assumption.
Qed.

(* Intersection is commutative.                                                 *)
Lemma inter_comm : forall (a b:Type) (r s:R a b), r ^ s = s ^ r.
Proof.
    intros a b r s. apply Ext. intros x y. unfold inter. split;
    intros [H1 H2]; split; assumption.
Qed.

(* Intersection is associative.                                                 *)
Lemma inter_assoc : forall (a b:Type) (r s t:R a b), (r ^ s) ^ t = r ^ (s ^ t).
Proof.
    intros a b r s t. apply Ext. intros x y. unfold inter. split.
    - intros [[H1 H2] H3]. split.
        + assumption.
        + split; assumption.
    - intros [H1 [H2 H3]]. split.
        + split; assumption.
        + assumption.
Qed.

Lemma conv_distrib_inter : forall (a b:Type) (r s:R a b), 
    conv (r ^ s) = conv r ^ conv s.
Proof.
    intros a b r s. apply Ext. intros x y. unfold inter, conv. split; auto.
Qed.
