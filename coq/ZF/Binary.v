Require Import ZF.Set.
Require Import ZF.Core.Equal.
Require Import ZF.Core.Equiv.

(* A binary class is simply a binary predicate on sets.                         *)
Definition Binary : Type := U -> U -> Prop.

(* Natural equivalence between binary classes.                                  *)
Definition binaryEquiv (F G:Binary) : Prop := forall x y, F x y <-> G x y.

(* The equivalence between binary classes is reflexive.                         *)
Proposition BinaryEquivRefl : forall (F:Binary), binaryEquiv F F.
Proof.
  intros F x y. split; intros H1; apply H1.
Qed.

(* The equivalence between binary classes is symmetric.                         *)
Proposition BinaryEquivSym : forall (F G:Binary),
  binaryEquiv F G -> binaryEquiv G F.
Proof.
  intros F G. unfold binaryEquiv. intros H1 x y. split; intros H2; apply H1, H2.
Qed.

(* The equivalence between binary classes is transitive.                        *)
Proposition BinaryEquivTran : forall (F G H:Binary),
  binaryEquiv F G -> binaryEquiv G H -> binaryEquiv F H.
Proof.
  intros F G H. unfold binaryEquiv. intros H1 H2 x y. split; intros H3.
  - apply H2, H1, H3.
  - apply H1, H2, H3.
Qed.

(* Notation "F == G" := (binaryEquiv F G)                                       *)
Global Instance BinaryEqual : Equal Binary := { equal := binaryEquiv }.

(* == is an equivalence relation                                                *)
Global Instance BinaryEquiv : Equiv Binary
  := { EquivRefl := BinaryEquivRefl
     ; EquivSym  := BinaryEquivSym
     ; EquivTran := BinaryEquivTran
     }.

Proposition BinaryEquivCharac : forall (F G:Binary),
  F == G <-> forall x y, F x y <-> G x y.
Proof.
  intros F G. split; intros H1.
  - apply H1.
  - unfold equal, BinaryEqual, binaryEquiv. apply H1.
Qed.
