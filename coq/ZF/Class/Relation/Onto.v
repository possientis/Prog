Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Fun.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.


(* F is a surjective function class from A to B.                                *)
Definition Onto (F A B:Class) : Prop := FunctionOn F A /\ range F :~: B.

Proposition IsFun : forall (F A B:Class), Onto F A B -> Fun F A B.
Proof.
  intros F A B H1. split. 1: apply H1. apply DoubleInclusion, EquivSym, H1.
Qed.

(* The direct image of a small class by a surjection F:A -> B is small.         *)
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

(* A surjection F:A -> B defined on a small class is small.                     *)
Proposition IsSmall : forall (F A B:Class),
  Onto F A B -> Small A -> Small F.
Proof.
  intros F A B H1. apply FunctionOn.IsSmall, H1.
Qed.

(* Two surjections are equal iff they have same domain and coincide pointwise.  *)
Proposition EquivCharac : forall (F A B G C D:Class),
  Onto F A B ->
  Onto G C D ->
  F :~: G   <->
  A :~: C /\ forall x, A x -> F!x = G!x.
Proof.
  intros F A B G C D H1 H2. apply FunctionOn.EquivCharac.
  - apply H1.
  - apply H2.
Qed.

(* If F and G are surjections then so is the composition G.F.                   *)
Proposition Compose : forall (F G A B C:Class),
  Onto F A B ->
  Onto G B C ->
  Onto (G :.: F) A C.
Proof.
  intros F G A B C [H1 H2] [H3 H4]. split.
  - apply FunctionOn.Compose with B; try assumption.
    apply Incl.EquivCompatL with B. 2: apply InclRefl.
    apply EquivSym. assumption.
  - apply EquivTran with (range G). 2: assumption.
    apply Compose.RangeIsSame, DoubleInclusion, EquivTran with B. 1: assumption.
    apply EquivSym, H3.
Qed.

Proposition EvalCharac : forall (F A B:Class) (a y:U),
  Onto F A B -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A B a y H1. apply FunctionOn.EvalCharac, H1.
Qed.

Proposition Satisfies : forall (F A B:Class) (a:U),
  Onto F A B -> A a -> F :(a,F!a):.
Proof.
  intros F A B a H1. apply FunctionOn.Satisfies, H1.
Qed.
