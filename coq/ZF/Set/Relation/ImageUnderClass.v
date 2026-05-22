Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Truncate.

Export ZF.Notation.Image.


Module CIN := ZF.Class.Incl.

(* Need to use 'truncate' as the image F[a] may not be small.                   *)
Definition image (F:Class) (a:U) : U := truncate F:[toClass a]:.

(* Notation "F :[ a ]:" := (image F a)                                          *)
Global Instance SetUnderClassImage : Image Class U U := { image := image }.

(* The class of the image equals the image of the class, when F is functional.  *)
Proposition ToClass : forall (F:Class) (a:U),
  Functional F -> toClass F:[a]: :~: F:[toClass a]:.
Proof.
  intros F a H1. apply Truncate.WhenSmall. apply Image.IsSmallR.
  1: assumption. apply SetIsSmall.
Qed.

(* The class of the image equals the image of the class, when F is small.       *)
Proposition ToClassWhenSmall : forall (F:Class) (a:U),
  Small F -> toClass F:[a]: :~: F:[toClass a]:.
Proof.
  intros F a H1. apply Truncate.WhenSmall, Image.IsSmallL. assumption.
Qed.

(* If F is functional and y is in the image of a, some x in a maps to y.        *)
Proposition Charac : forall (F:Class) (a y:U),
  Functional F ->  y :< F:[a]: -> exists x, x :< a /\ F :(x,y):.
Proof.
  intros F a y H1 H2. apply ToClass in H2. 2: assumption.
  destruct H2 as [x [H2 H3]]. exists x. split; assumption.
Qed.

(* If F is functional and x in a maps to y, then y belongs to the image.        *)
Proposition CharacRev : forall (F:Class) (a x y:U),
  Functional F -> x :< a -> F :(x,y): -> y :< F:[a]:.
Proof.
  intros F a x y H1 H2 H3. apply ToClass. 1: assumption.
  exists x. split; assumption.
Qed.

(* The image is compatible with class equivalence in the function argument.     *)
Proposition EquivCompat : forall (F G:Class) (a:U),
  F :~: G -> F:[a]: = G:[a]:.
Proof.
  intros F G a H1. apply Truncate.EquivCompat, Image.EquivCompatL. assumption.
Qed.

(* The image is compatible with inclusion in both the function and set.         *)
Proposition InclCompat : forall (F G:Class) (a b:U), Functional G ->
  F :<=: G -> a :<=: b -> F:[a]: :<=: G:[b]:.
Proof.
  intros F G a b H1 H2 H3 y H4.
  apply Charac in H4. 2: { apply Functional.InclCompat with G; assumption. }
  destruct H4 as [x [H4 H5]]. apply CharacRev with x. 1: assumption.
  - apply H3. assumption.
  - apply H2. assumption.
Qed.

(* The image is left-compatible with class inclusion in the function argument.  *)
Proposition InclCompatL : forall (F G:Class) (a:U), Functional G ->
  F :<=: G -> F:[a]: :<=: G:[a]:.
Proof.
  intros F G a H1 H2. apply InclCompat; try assumption. apply ZF.Set.Incl.Refl.
Qed.

(* The image is right-compatible with inclusion in the set argument.            *)
Proposition InclCompatR : forall (F:Class) (a b:U), Functional F ->
  a :<=: b -> F:[a]: :<=: F:[b]:.
Proof.
  intros F a b H1 H2. apply InclCompat; try assumption. apply CIN.Refl.
Qed.

(* The image of the empty set under any class is the empty set.                 *)
Proposition WhenEmpty : forall (F:Class) (a:U),
  a = :0: -> F:[a]: = :0:.
Proof.
  intros F a H1. rewrite H1. apply Truncate.WhenEmpty.
  intros x. split; intros H2.
  - destruct H2 as [y [H2 H3]]. apply Empty.Charac in H2. contradiction.
  - contradiction.
Qed.

(* If F is functional and x is in both its domain and a, then F!x is in F[a].   *)
Proposition IsIn : forall (F:Class) (a x:U),
  Functional F    ->
  domain F x      ->
  x :< a          ->
  F!x :< F:[a]:.
Proof.
  intros F a x H1 H2 H3. apply CharacRev with x; try assumption.
  apply EvalOfClass.Satisfies; assumption.
Qed.
