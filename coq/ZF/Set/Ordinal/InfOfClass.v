Require Import ZF.Class.Core.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Inf.
Require Import ZF.Set.Core.
Require Import ZF.Set.InterOfClass.

(* The infimum of the class A.                                                  *)
Definition inf (A:Class) : U := inter (A :/\: On).

Proposition Charac : forall (A:Class) (x y:U),
  x :< inf A  ->
  A y         ->
  On y        ->
  x :< y.
Proof.
  intros A x y H1 H2 H3. apply InterOfClass.Charac with (A :/\: On).
  1: assumption. split; assumption.
Qed.

Proposition CharacRev : forall (A:Class) (x:U),
  A :/\: On  :<>: :0:               ->
  (forall y, A y -> On y -> x :< y) ->
  x :< inf A.
Proof.
  intros A x H1 H2. apply InterOfClass.CharacRev. 1: assumption.
  intros y [H3 H4]. apply H2; assumption.
Qed.

(* The infimum (as class) of the class is the class of the infimum (as set).    *)
Proposition ToClass : forall (A:Class),
  Class.Ordinal.Inf.inf A :~: toClass (inf A).
Proof.
  intros A. apply ZF.Set.InterOfClass.ToClass.
Qed.

(* The infimum of a class of ordinals coincide with its intersection.           *)
Proposition WhenHasOrdinalElem : forall (A:Class),
  A :<=: On -> inf A = inter A.
Proof.
  intros A H1. unfold inf. apply InterOfClass.EquivCompat.
  apply Class.Inter2.WhenInclL. assumption.
Qed.
