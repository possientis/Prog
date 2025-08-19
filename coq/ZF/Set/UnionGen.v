Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.UnionGen.
Export ZF.Notation.UnionGen.

(* The generalized union \/_{x :< a} b(x)                                       *)
Definition unionGen (a b:U) : U := :\/:_{a} (toClass b).

(* Notation ":\/:_{ a } b" := (unionGen a b)                                    *)
Global Instance SetUnionGen : UnionGen U U := {unionGen := unionGen }.

Proposition Charac : forall (a b y:U),
  y :< :\/:_{a} b <-> exists x, x :< a /\ y :< b!x.
Proof.
  intros a b. apply UnionGenOfClass.Charac.
Qed.

Proposition EqualCharac : forall (a b c:U),
  (forall x, x :< a -> b!x = c!x) -> :\/:_{a} b = :\/:_{a} c.
Proof.
  intros a b c H1. apply DoubleInclusion. split; intros y H2;
  apply Charac in H2; destruct H2 as [x [H2 H3]]; apply Charac;
  exists x; split; try assumption.
  - rewrite <- H1; assumption.
  - rewrite H1; assumption.
Qed.
