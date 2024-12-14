Require Import ZF.Set.
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

Global Instance BinaryEquiv : Equiv Binary
  := { equiv     := binaryEquiv
     ; EquivRefl := BinaryEquivRefl
     ; EquivSym  := BinaryEquivSym
     ; EquivTran := BinaryEquivTran
     }.

Proposition BinaryEquivCharac : forall (F G:Binary),
  F == G <-> forall x y, F x y <-> G x y.
Proof.
  intros F G. split; intros H1.
  - apply H1.
  - unfold equiv, BinaryEquiv, binaryEquiv. apply H1.
Qed.
