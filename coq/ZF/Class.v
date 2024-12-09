Require Import ZF.Core.
Require Import ZF.Core.Equiv.

(* A class is simply a predicate on sets.                                       *)
Definition Class : Type := U -> Prop.

(* Natural equivalence between classes.                                         *)
Definition classEquiv (P Q:Class) : Prop := forall x, P x <-> Q x.

(* The equivalence between classes is reflexive.                                *)
Proposition ClassEquivRefl : forall (P:Class), classEquiv P P.
Proof.
  intros P x. split; intros H1; apply H1.
Qed.

(* The equivalence between classes is symmetric.                                *)
Proposition ClassEquivSym : forall (P Q:Class),
  classEquiv P Q -> classEquiv Q P.
Proof.
  intros P Q. unfold classEquiv. intros H1 x. split; intros H2; apply H1, H2.
Qed.

(* The equivalence between classes is transitive.                               *)
Proposition ClassEquivTran : forall (P Q R:Class),
  classEquiv P Q -> classEquiv Q R -> classEquiv P R.
Proof.
  intros P Q R. unfold classEquiv. intros H1 H2 x. split; intros H3.
  - apply H2, H1, H3.
  - apply H1, H2, H3.
Qed.

Global Instance ClassEquiv : Equiv Class
  := { equiv     := classEquiv
     ; EquivRefl := ClassEquivRefl
     ; EquivSym  := ClassEquivSym
     ; EquivTran := ClassEquivTran
     }.

Proposition ClassEquivCharac : forall (P Q:Class),
  P == Q <-> forall x, P x <-> Q x.
Proof.
  intros P Q. split; intros H1.
  - apply H1.
  - unfold equiv, ClassEquiv, classEquiv. apply H1.
Qed.

(* A set can be viewed as a class.                                              *)
Definition toClass (a:U) : Class := fun x => x :< a.
