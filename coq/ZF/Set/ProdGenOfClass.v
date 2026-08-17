Require Import ZF.Class.Equiv.
Require Import ZF.Class.ProdGen.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.FunctionOn.


Require Import ZF.Notation.ProdGen.
Export ZF.Notation.ProdGen.


(* The generalized product prd_{x :< a} A(x)                                       *)
Definition prodGen (a:U) (A:Class) : U := fromClass (:prd:_{a} A)
  (ProdGen.IsSmall A a).

(* Notation ":prd:_{ a } A" := (prodGen a A)                                    *)
Global Instance ProdGenOfClass : ProdGen U Class U := { prodGen := prodGen }.

Proposition Charac : forall (A:Class) (a f:U),
  f :< :prd:_{a} A <-> FunctionOn f a /\ forall x, x :< a -> f!x :< A!x.
Proof.
  intros A a f. split; intros H1.
  - apply FromClass.Charac in H1. assumption.
  - apply FromClass.Charac. assumption.
Qed.
