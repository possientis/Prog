Require Import ZF.Binary.
Require Import ZF.Binary.Functional.
Require Import ZF.Binary.Image.
Require Import ZF.Class.
Require Import ZF.Class.Small.
Require Import ZF.Core.Image.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.

(* The set defined by the class F[P] when F is functional and P is small.       *)
Definition replaceSet (F:Binary) (P:Class) (p:Functional F) (q:Small P) : U
  := fromClass F:[P]: (ImageSmall F P p q).

(* Characterisation of the elements of the set associated with the class F[P].  *)
Proposition ReplaceCharac : forall (F:Binary)(P:Class)(p:Functional F)(q:Small P),
  forall y, y :< (replaceSet F P p q) <-> F:[P]: y.
Proof.
  unfold replaceSet. intros F P p q. apply FromClassCharac.
Qed.
