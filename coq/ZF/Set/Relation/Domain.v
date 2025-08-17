Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.


(* The domain of a set.                                                         *)
Definition domain (f:U) : U := fromClass (Domain.domain (toClass f))
  (Domain.IsSmall (toClass f) (SetIsSmall f)).

(* The class of the domain is the domain of the class.                          *)
Proposition ToClass : forall (f:U),
  toClass (domain f) :~: Class.Relation.Domain.domain (toClass f).
Proof.
  intros f. apply ToFromClass.
Qed.

Proposition Charac : forall (f x: U),
  x :< domain f <-> exists y, :(x,y): :< f.
Proof.
  intros f x. split; intros H1.
  - apply FromClass.Charac in H1. destruct H1 as [y H1]. exists y. assumption.
  - destruct H1 as [y H1]. apply FromClass.Charac. exists y. assumption.
Qed.

(* The domain is compatible with set inclusion.                                 *)
Proposition InclCompat : forall (f g:U),
  f :<=: g -> domain f :<=: domain g.
Proof.
  intros f g H1 x H2. apply Charac in H2. destruct H2 as [y H2].
  apply Charac. exists y. apply H1. assumption.
Qed.

Proposition WhenEmpty : domain :0: = :0:.
Proof.
  apply DoubleInclusion. split; intros x H1.
  - apply Charac in H1. destruct H1 as [y H1].
    apply Empty.Charac in H1. contradiction.
  - apply Empty.Charac in H1. contradiction.
Qed.
