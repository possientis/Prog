Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.
Require Import ZF.Class.InterGen.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Relation.Eval.

Require Import ZF.Notation.InterGen.
Export ZF.Notation.InterGen.

(* The generalized intersection /\_{x :< a} A(x)                                *)
Definition interGen (a:U) (A:Class) : U := fromClass (:/\:_{toClass a} A)
  (InterGen.IsSmall (toClass a) A).

(* Notation ":/\:_{ a } A" := (interGen a A)                                    *)
Global Instance SetInterGenOfClass : InterGen U Class := {interGen := interGen }.

Proposition Charac : forall (A:Class) (a x y:U),
  y :< :/\:_{a} A ->
  x :< a          ->
  y :< A!x.
Proof.
  intros A a x y H1 H2. apply FromClass.Charac in H1.
  apply InterGen.Charac with (toClass a); assumption.
Qed.

Proposition CharacRev : forall (A:Class) (a y:U),
  a <> :0:                       ->
  (forall x, x :< a -> y :< A!x) ->
  y :< :/\:_{a} A.
Proof.
  intros A a y H1 H2. apply Empty.NotEmptyToClass in H1.
  apply FromClass.Charac, InterGen.CharacRev; assumption.
Qed.
