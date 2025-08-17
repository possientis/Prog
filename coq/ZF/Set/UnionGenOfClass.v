Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.
Require Import ZF.Class.UnionGen.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Relation.Eval.

Require Import ZF.Notation.UnionGen.
Export ZF.Notation.UnionGen.

(* The generalized union \/_{x :< a} A(x)                                       *)
Definition unionGen (a:U) (A:Class) : U := fromClass (:\/:_{toClass a} A)
  (UnionGen.IsSmall (toClass a) A (SetIsSmall a)).

(* Notation ":\/:_{ a } A" := (unionGen a A)                                    *)
Global Instance SetUnionGenOfClass : UnionGen U Class := {unionGen := unionGen }.

Proposition Charac : forall (A:Class) (a y:U),
  y :< :\/:_{a} A <-> exists x, x :< a /\ y :< A!x.
Proof.
  intros A a y. split; intros H1.
  - apply FromClass.Charac in H1. apply UnionGen.Charac in H1. assumption.
  - apply FromClass.Charac, UnionGen.Charac. assumption.
Qed.
