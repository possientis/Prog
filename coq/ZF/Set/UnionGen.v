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

Proposition IsIncl : forall (a b x:U),
  x :< a -> b!x :<=: :\/:_{a} b.
Proof.
  intros a b. apply UnionGenOfClass.IsIncl.
Qed.

Proposition InclCompat : forall (a b c d:U),
  a :<=: c                            ->
  (forall x, x :< a -> b!x :<=: d!x)  ->
  :\/:_{a} b  :<=: :\/:_{c} d.
Proof.
  intros a b c d H1 H2 y H3.
  apply Charac in H3. destruct H3 as [x [H3 H4]].
  apply Charac. exists x. split.
  - apply H1. assumption.
  - apply H2; assumption.
Qed.

Proposition InclCompatL : forall (a b c:U),
  a :<=: c -> :\/:_{a} b :<=: :\/:_{c} b.
Proof.
  intros a b c H1. apply InclCompat. 1: assumption.
  intros x _. apply Incl.Refl.
Qed.

Proposition InclCompatR : forall (a b c:U),
  (forall x, x :< a -> b!x :<=: c!x)  -> :\/:_{a} b :<=: :\/:_{a} c.
Proof.
  intros a b c H1. apply InclCompat. 2: assumption.
  apply Class.Incl.Refl.
Qed.
