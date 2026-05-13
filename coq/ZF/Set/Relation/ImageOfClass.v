Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.

Export ZF.Notation.Image.


Module CIN := ZF.Class.Incl.

Definition image (f:U) (A:Class) : U := fromClass (toClass f) :[A]:
  (Image.IsSmall' (toClass f) A (SetIsSmall f)).


(* Notation "f :[ A ]:" := (image f A)                                          *)
Global Instance SetOfClassImage : Image U Class U := { image := image }.

(* The class of the image equals the image of the class by the class.           *)
Proposition ToClass : forall (A:Class) (f:U),
  toClass f:[A]: :~: (toClass f) :[A]:.
Proof.
  intros A f. apply FromClass.ToClass.
Qed.

(* y belongs to the image iff some x satisfying A maps to y under f.            *)
Proposition Charac : forall (A:Class) (f y:U),
  y :< f:[A]: <-> exists x, A x /\ :(x,y): :< f.
Proof.
  intros A f y. split; intros H1.
  - apply FromClass.Charac in H1. destruct H1 as [x H1]. exists x. assumption.
  - destruct H1 as [x H1]. apply FromClass.Charac. exists x. assumption.
Qed.

(* The image is compatible with class equivalence.                              *)
Proposition EquivCompat : forall (A B:Class) (f:U),
  A :~: B -> f:[A]: = f:[B]:.
Proof.
  intros A B f H1. apply Incl.Double. split; intros y H2; apply Charac in H2;
  destruct H2 as [x [H2 H3]]; apply Charac; exists x; split; try assumption;
  apply H1; assumption.
Qed.

(* The image is compatible with inclusion in both the function and class.       *)
Proposition InclCompat : forall (A B:Class) (f g:U),
  f :<=: g -> A :<=: B -> f:[A]: :<=: g:[B]:.
Proof.
  intros A B f g H1 H2 y H3. apply Charac in H3. destruct H3 as [x [H3 H4]].
  apply Charac. exists x. split.
  - apply H2. assumption.
  - apply H1. assumption.
Qed.

(* The image is left-compatible with inclusion in the function argument.        *)
Proposition InclCompatL : forall (A:Class) (f g:U),
  f :<=: g -> f:[A]: :<=: g:[A]:.
Proof.
  intros A f g H1. apply InclCompat. 1: assumption.
  apply CIN.Refl.
Qed.

(* The image is right-compatible with class inclusion in the domain argument.   *)
Proposition InclCompatR : forall (A B:Class) (f:U),
  A :<=: B -> f:[A]: :<=: f:[B]:.
Proof.
  intros A B f. apply InclCompat, ZF.Set.Incl.Refl.
Qed.

(* The image of an empty class under any function is the empty set.             *)
Proposition WhenEmpty : forall (A:Class) (f:U),
  A :~: :0: -> f:[A]: = :0:.
Proof.
  intros A f H1. apply Incl.Double. split; intros y H2.
  - apply Charac in H2. destruct H2 as [x [H2 H3]].
    apply H1 in H2. contradiction.
  - apply Empty.Charac in H2. contradiction.
Qed.
