Require Import ZF.Class.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Image.
Require Import ZF.Class.Small.
Require Import ZF.Core.Image.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Replace.

(* If P is functional and Q is small, then P:[Q]: is small.                     *)
Proposition ReplaceSmall : forall (P Q:Class),
  Functional P -> Small Q -> Small P :[Q]:.
Proof.
  intros P Q. apply Replace.ReplaceSmall.
Qed.

(* The set defined by the class P[Q] when P is functional and Q is small.       *)
Definition replaceSet (P Q:Class) (p:Functional P) (q:Small Q) : U
  := fromClass P:[Q]: (ReplaceSmall P Q p q).

(* Characterisation of the elements of the set associated with the class P[Q].  *)
Proposition ReplaceCharac : forall (P Q:Class)(p:Functional P)(q:Small Q),
  forall y, y :< (replaceSet P Q p q) <-> P:[Q]: y.
Proof.
  unfold replaceSet. intros P Q p q. apply FromClassCharac.
Qed.
