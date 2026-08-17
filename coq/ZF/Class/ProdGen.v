
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Map.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.ProdGen.
Export ZF.Notation.ProdGen.

(* The generalized product prd_{x :< a} A(x).                                   *)
Definition prodGen (a:U) (A:Class) : Class := fun f =>
  FunctionOn f a /\ forall x, x :< a -> f!x :< A!x.

(* Notation ":prd:_{ a } A" := (prodGen a A)                                    *)
Global Instance ProdGenClass : ProdGen U Class Class := { prodGen := prodGen }.

(* The generalized product over a set-indexed family is small.                  *)
Proposition IsSmall : forall (A:Class) (a:U),
  Small (:prd:_{ a } A).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros A a.
  (* The product is included in the ordinary map set into the family union.     *)
  assert (:prd:_{a} A :<=: toClass (map a (:\/:_{a} A))) as H1. {
    intros f H1. destruct H1 as [H1 H2]. apply Map.CharacMap.
    apply Fun.FromFunctionOn. 1: assumption.
    (* Each product value lies in its fibre, hence in the union of all fibres.  *)
    intros x H3. apply UnionGenOfClass.IsIncl with x. 1: assumption.
    apply H2. assumption. }
  (* Since the map set is a set, so is any subclass of it.                      *)
  assert (Small (toClass (map a (:\/:_{a} A)))) as H2. { apply Small.SetIsSmall. }
  apply Small.InclCompat with (toClass (map a (:\/:_{a} A))); assumption.
Qed.

