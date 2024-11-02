Declare Scope ZF_Include_scope.
Open    Scope ZF_Include_scope.

Require Import Logic.ZF.Core.
Require Import Logic.ZF.Extensionality.

(* Inclusion predicate between two sets.                                        *)
Definition Incl (a b:U) : Prop := forall x, x :< a -> x :< b.

Notation "a :<=: b" := (Incl a b)
  (at level 5, no associativity) : ZF_Include_scope.

(* Strict inclusion predicate.                                                  *)
Definition InclStrict (a b:U) : Prop := a :<=: b /\ ~a = b.

Notation "a :<: b" := (InclStrict a b)
  (at level 5, no associativity) : ZF_Include_scope.

(* Two sets are equal if and only if they are subsets of each other.            *)
Proposition DoubleInclusion : forall (a b:U),
  a = b <-> a :<=: b /\ b :<=: a.
Proof.
  intros a b. unfold Incl. split.
  - intros H1. split; intros x Hx.
    + rewrite <- H1. apply Hx.
    + rewrite H1. apply Hx.
  - intros [H1 H2]. apply Extensionality. intros x. split.
    + apply H1.
    + apply H2.
Qed.
