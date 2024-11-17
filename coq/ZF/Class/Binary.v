Declare Scope ZF_Class_Binary_scope.
Open    Scope ZF_Class_Binary_scope.

Require Import ZF.Axiom.Core.
Require Import ZF.Class.Class.
Require Import ZF.Core.Equiv.

(* A binary class is simply a binary predicate on sets.                         *)
Definition Binary : Type := U -> U -> Prop.

(* Natural equivalence between binary classes.                                  *)
Definition binaryEquiv (F G:Binary) : Prop := forall x y, F x y <-> G x y.

Global Instance BinaryEquiv : Equiv Binary := {
  equiv := binaryEquiv
}.

Proposition BinaryEquivCharac : forall (F G:Binary),
  F == G <-> forall x y, F x y <-> G x y.
Proof.
  intros F G. split; intros H1.
  - apply H1.
  - unfold equiv, BinaryEquiv, binaryEquiv. apply H1.
Qed.

(* Predicate expressing the fact that a binary class is functional.             *)
Definition Functional (F:Binary) : Prop :=
  forall x, forall y, forall z, F x y -> F x z -> y = z.

(* Direct image of a set a by a binary class F.                                 *)
Definition Image (F:Binary) (a:U) : Class := fun y =>
  exists x, x :< a /\ F x y.

Notation "R [ a ]" := (Image R a)
  (at level 0, no associativity) : ZF_Class_Binary_scope.

(* The converse of a binary class.                                              *)
Definition converse (F:Binary) : Binary := fun x y => F y x.

(* Take the converse is an indempotent operation.                               *)
(* Note that we have actual equality here, not just equivalence.                *)
Proposition ConverseIdempotent : forall (F:Binary),
  converse (converse F) = F.
Proof.
  intros F. unfold converse. reflexivity.
Qed.

(* The converse operation is compatible with equivalence.                       *)
Proposition ConverseEquivCompat : EquivCompat converse.
Proof.
  intros F G H1 x y. unfold converse. apply H1.
Qed.
