Declare Scope ZF_Class_Binary_scope.
Open    Scope ZF_Class_Binary_scope.

Require Import ZF.Core.
Require Import ZF.Class.
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

(* Domain of a binary class.                                                    *)
Definition domain (F:Binary) : Class := fun x => exists y, F x y.

(* Range of a binary class.                                                    *)
Definition range (F:Binary) : Class := fun y => exists x, F x y.

(* Predicate expressing the fact that a binary class is functional.             *)
Definition Functional (F:Binary) : Prop :=
  forall x, forall y, forall z, F x y -> F x z -> y = z.

(* Restricting a binary class F to a class P.                                   *)
Definition restrict (F:Binary) (P:Class) : Binary := fun x y =>
  P x /\ F x y.

Notation "F :|: P" := (restrict F P)
  (at level 13, left associativity) : ZF_Class_Binary_scope.

(* Direct image of a set a by a binary class F.                                 *)
Definition image (F:Binary) (a:U) : Class := fun y =>
  exists x, x :< a /\ F x y.

Notation "F :[ a ]:" := (image F a)
  (at level 0, no associativity) : ZF_Class_Binary_scope.

(* Image is the range of the restriction.                                       *)
(* This is an equal equality, not just equivalence.                             *)
Proposition ImageIsRestriction : forall (F:Binary) (a:U),
  F:[a]: = range (F:|: (toClass a)).
Proof.
  intros F a. unfold image, range, restrict. reflexivity.
Qed.

(* The converse of a binary class.                                              *)
Definition converse (F:Binary) : Binary := fun x y => F y x.

(* Taking the converse is an indempotent operation.                             *)
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

(* Composition of two binary relation.                                          *)
Definition compose (G F:Binary) : Binary := fun x y =>
  exists z, F x z /\ G z y.

Notation "G :.: F" := (compose G F)
  (at level 11, right associativity) : ZF_Class_Binary_scope.
