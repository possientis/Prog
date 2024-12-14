Require Import ZF.Class.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Functional.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* A class is 'one-to-one' if both itself and its converse are functional.      *)
Definition OneToOne (P:Class) : Prop := Functional P /\ Functional (converse P).

Proposition OneToOneCharac1 : forall (P:Class), OneToOne P ->
  forall x, forall y, forall z, P :(x,y): -> P :(x,z): -> y = z.
Proof.
  intros P H1. apply FunctionalCharac, H1.
Qed.

Proposition OneToOneCharac2 : forall (P:Class), OneToOne P ->
  forall x, forall y, forall z, P :(y,x): -> P :(z,x): -> y = z.
Proof.
  intros P H1 x y z H3 H4. destruct H1 as [H1 H2].
  apply FunctionalCharac with (converse P) x.
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


