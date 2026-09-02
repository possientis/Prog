Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.InterGenOfClass.
Require Import ZF.Set.Relation.Eval.

Require Import ZF.Notation.InterGen.
Export ZF.Notation.InterGen.

(* The generalized intersection /\_{x :< a} b(x)                                *)
Definition interGen (a b:U) : U := :/\:_{a} (toClass b).

(* Notation ":/\:_{ a } b" := (interGen a b)                                    *)
Global Instance SetInterGen : InterGen U U := {interGen := interGen }.

Proposition Charac : forall (a b x y:U),
  y :< :/\:_{a} b ->
  x :< a          ->
  y :< b!x.
Proof.
  intros a b. apply InterGenOfClass.Charac.
Qed.

Proposition CharacRev : forall (a b y:U),
  a <> :0:                       ->
  (forall x, x :< a -> y :< b!x) ->
  y :< :/\:_{a} b.
Proof.
  intros a b. apply InterGenOfClass.CharacRev.
Qed.

