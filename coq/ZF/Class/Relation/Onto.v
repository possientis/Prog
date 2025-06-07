Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Fun.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Small.

(* F is a surjective function class from A to B.                                *)
Definition Onto (F A B:Class) : Prop := FunctionOn F A /\ range F :~: B.

Proposition IsFun : forall (F A B:Class), Onto F A B -> Fun F A B.
Proof.
  intros F A B H1. split. 1: apply H1. apply DoubleInclusion, EquivSym, H1.
Qed.

Proposition ImageIsSmall : forall (F A B C:Class),
  Onto F A B -> Small C -> Small F:[C]:.
Proof.
  intros F A B C H1. apply FunctionOn.ImageIsSmall with A, H1.
Qed.

(* A surjection F:A -> B is a subclass of AxB.                                  *)
Proposition InclInProduct : forall (F A B:Class),
  Onto F A B -> F :<=: A :x: B.
Proof.
  intros F A B H1. apply Fun.InclInProduct, IsFun. assumption.
Qed.


