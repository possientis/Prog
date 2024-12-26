Require Import ZF.Binary.
Require Import ZF.Binary.Converse.
Require Import ZF.Binary.Functional.
Require Import ZF.Binary.OneToOne.
Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Converse.
Require Import ZF.Class.FromBinary.
Require Import ZF.Class.Functional.
Require Import ZF.Core.Dot.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* A class is one-to-one if both itself and its converse are functional.        *)
Definition OneToOne (P:Class) : Prop := Functional P /\ Functional (converse P).

Proposition OneToOneFromBinary : forall (P:Class),
  OneToOne P <-> Binary.OneToOne.OneToOne (toBinary P).
Proof.
  intros P. unfold Binary.OneToOne.OneToOne, OneToOne, Functional,converse.
  split; intros [H1 H2].
  - split.
    + assumption.
    + apply FunctionalEquivCompat with
        (toBinary (fromBinary (Binary.Converse.converse (toBinary P)))). 2: apply H2.
      apply ToFromBinary.
  - split.
    + assumption.
    + apply FunctionalEquivCompat with
        (Binary.Converse.converse (toBinary P)). 2: apply H2.
      apply BinaryEquivSym, ToFromBinary.
Qed.

Proposition OneToOneCharac1 : forall (P:Class), OneToOne P ->
  forall x, forall y, forall z, P :(x,y): -> P :(x,z): -> y = z.
Proof.
  intros P H1. apply FunctionalCharac1, H1.
Qed.

Proposition OneToOneCharac2 : forall (P:Class), OneToOne P ->
  forall x, forall y, forall z, P :(y,x): -> P :(z,x): -> y = z.
Proof.
  intros P H1 x y z H3 H4. destruct H1 as [H1 H2].
  apply FunctionalCharac1 with (converse P) x.
  - apply H2.
  - apply ConverseCharac2, H3.
  - apply ConverseCharac2, H4.
Qed.

(* When two ordered pairs belong to a one-to-one class, equality between the    *)
(* first coordinates is equivalent to equality between the second coordinates.  *)
Proposition OneToOneCoordEquiv : forall (P:Class) (x1 x2 y1 y2:U),
  OneToOne P -> P :(x1,y1): -> P :(x2,y2): -> x1 = x2 <-> y1 = y2.
Proof.
  intros P x1 x2 y1 y2 H3 H1 H2. split; intros H4.
  - subst. apply OneToOneCharac1 with P x2; assumption.
  - subst. apply OneToOneCharac2 with P y2; assumption.
Qed.

Proposition ComposeIsOneToOne : forall (P Q:Class),
  OneToOne P -> OneToOne Q -> OneToOne (Q :.: P).
Proof.
  intros P Q [Hp Gp] [Hq Gq]. split.
  - apply ComposeIsFunctional; assumption.
  - apply FunctionalEqualCompat with (converse P :.: converse Q).
    + apply ClassEquivSym. apply ConverseOfCompose.
    + apply ComposeIsFunctional; assumption.
Qed.
