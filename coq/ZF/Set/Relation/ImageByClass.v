Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Truncate.

Export ZF.Notation.Image.

(* Need to use 'truncate' as the image F[a] may not be small.                   *)
Definition image (F:Class) (a:U) : U := truncate F:[toClass a]:.

(* Notation "F :[ a ]:" := (image F a)                                          *)
Global Instance SetImageByClass : Image Class U := { image := image }.

Proposition ToClass : forall (F:Class) (a:U),
  Functional F -> toClass F:[a]: :~: F:[toClass a]:.
Proof.
  intros F a H1. apply Truncate.WhenSmall. apply Image.IsSmall.
  1: assumption. apply SetIsSmall.
Qed.

Proposition Charac : forall (F:Class) (a y:U),
  Functional F ->  y :< F:[a]: -> exists x, x :< a /\ F :(x,y):.
Proof.
  intros F a y H1 H2. apply ToClass in H2. 2: assumption.
  destruct H2 as [x [H2 H3]]. exists x. split; assumption.
Qed.

Proposition CharacRev : forall (F:Class) (a x y:U),
  Functional F -> x :< a -> F :(x,y): -> y :< F:[a]:.
Proof.
  intros F a x y H1 H2 H3. apply ToClass. 1: assumption.
  exists x. split; assumption.
Qed.

Proposition EquivCompat : forall (F G:Class) (a:U),
  F :~: G -> F:[a]: = G:[a]:.
Proof.
  intros F G a H1. apply Truncate.EquivCompat, Image.EquivCompatL. assumption.
Qed.

Proposition InclCompat : forall (F G:Class) (a:U), Functional G ->
  F :<=: G -> F:[a]: :<=: G:[a]:.
Proof.
  intros F G a H1 H2 y H3.
  apply Charac in H3. 2: { apply Functional.InclCompat with G; assumption. }
  destruct H3 as [x [H3 H4]]. apply CharacRev with x; try assumption.
  apply H2. assumption.
Qed.
