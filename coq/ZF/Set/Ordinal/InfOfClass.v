Require Import ZF.Class.Equiv.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.IsSetOf.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Inf.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InterOfClass.
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
Proposition WhenOrdinalElem : forall (A:Class),
  A :<=: On -> inf A = inter A.
Proof.
  intros A H1. unfold inf. apply InterOfClass.EquivCompat.
  apply Class.Inter2.WhenInclL. assumption.
Qed.

(* Restricting a class to its ordinal elements leads to the same infimum.       *)
Proposition InterOn : forall (A:Class), inf A = inf (A :/\: On).
Proof.
  intros A. rewrite WhenOrdinalElem with (A :/\: On). 1: reflexivity.
  apply Inter2.IsInclR.
Qed.

(* The infimum of a class is an ordinal.                                        *)
Proposition IsOrdinal : forall (A:Class), Ordinal (inf A).
Proof.
  intros A. apply InterOfClass.IsOrdinal, Inter2.IsInclR.
Qed.

(* The infimum of a class of ordinals is a lower-bound of the class.            *)
Proposition IsLowerBound : forall (A:Class) (a:U),
  A :<=: On -> A a -> inf A :<=: a.
Proof.
  intros A a H1 H2. apply Incl.EquivCompatL with  (Class.Ordinal.Inf.inf A).
  1: apply ToClass. apply Class.Ordinal.Inf.IsLowerBound; assumption.
Qed.

(* The infimum of a class is a lower-bound of its ordinal elements.             *)
Proposition IsLowerBoundOrd : forall (A:Class) (a:U), Ordinal a ->
  A a -> inf A :<=: a.
Proof.
  intros A a H1 H2. rewrite InterOn. apply IsLowerBound.
  1: apply Inter2.IsInclR. split; assumption.
Qed.

(* The infimum of a non-empty class of ordinals is the largest lower-bound.     *)
Proposition IsLargest : forall (A:Class) (a:U),
  A :<=: On                     ->
  A :<>: :0:                    ->
  (forall b, A b  -> a :<=: b)  ->
  a :<=: inf A.
Proof.
  intros A a H1 H2 H3. apply Incl.EquivCompatR with  (Class.Ordinal.Inf.inf A).
  1: apply ToClass. apply Class.Ordinal.Inf.IsLargest; assumption.
Qed.

(* The infimum of a class with an ordinal is largest lower-bound of its ordinals*)
Proposition IsLargestOrd : forall (A:Class) (a:U),
  A :/\: On :<>: :0:                        ->
  (forall b, Ordinal b -> A b -> a :<=: b)  ->
  a :<=: inf A.
Proof.
  intros A a H1 H2. rewrite InterOn. apply IsLargest. 2: assumption.
  - apply Inter2.IsInclR.
  - intros b [H3 H4]. apply H2; assumption.
Qed.

(* The infimum of a non-empty class of ordinals belongs to the class.           *)
Proposition IsIn : forall (A:Class),
  A :<=: On -> A :<>: :0: -> A (inf A).
Proof.
  intros A H1 H2.
  assert (IsSetOf (Class.Ordinal.Inf.inf A) (inf A)) as H3. {
    apply Class.IsSetOf.ToClass, Equiv.Sym, ToClass. }
  apply Class.Ordinal.Inf.IsIn; assumption.
Qed.

(* The infimum of a class with an ordinal belongs to the class.                 *)
Proposition IsInOrd : forall (A:Class),
  A :/\: On :<>: :0: -> A (inf A).
Proof.
  intros A H1. rewrite InterOn. apply Inter2.IsInclL with On. apply IsIn.
  2: assumption. apply Inter2.IsInclR.
Qed.

Proposition WhenOrdinal : forall (A:Class) (a:U),
  Class.Ordinal.Core.Ordinal A  ->
  Ordinal a                     ->
  A :\: toClass a :<>: :0:      ->
  inf (A :\: toClass a) = a.
Proof.
  intros A a H1 H2 H3. symmetry. apply EqualToClass.
  apply Equiv.Tran with (Class.Ordinal.Inf.inf (A :\: toClass a)).
  2: apply ToClass. apply Class.Ordinal.Inf.WhenOrdinal; assumption.
Qed.

Proposition IsEMinimal : forall (A:Class) (a:U),
  A :<=: On   ->
  A :<>: :0:  ->
  a = inf A <-> Minimal E A a.
Proof.
  intros A a H1 H2. split; intros H3.
  - apply Inf.IsEMinimal; try assumption. rewrite H3. apply Equiv.Sym, ToClass.
  - apply Inf.IsEMinimal in H3; try assumption. apply EqualToClass.
    apply Equiv.Tran with (Class.Ordinal.Inf.inf A). 1: assumption.
    apply ToClass.
Qed.
