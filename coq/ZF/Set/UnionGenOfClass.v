Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.
Require Import ZF.Class.UnionGen.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Relation.EvalOfClass.

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

Proposition EqualCharac : forall (A B:Class) (a:U),
  (forall x, x :< a -> A!x = B!x) -> :\/:_{a} A = :\/:_{a} B.
Proof.
  intros a A B H1. apply DoubleInclusion. split; intros y H2;
  apply Charac in H2; destruct H2 as [x [H2 H3]]; apply Charac;
  exists x; split; try assumption.
  - rewrite <- H1; assumption.
  - rewrite H1; assumption.
Qed.

Proposition EquivCompat : forall (A B:Class) (a:U),
  A :~: B -> :\/:_{a} A = :\/:_{a} B.
Proof.
  intros A B a H1.
  apply EqualCharac. intros x H2.
  apply EvalOfClass.EquivCompat. assumption.
Qed.

Proposition IsIncl : forall (A:Class) (a x:U),
  x :< a -> A!x :<=: :\/:_{a} A.
Proof.
  intros A a x H1 y H2. apply Charac. exists x. split; assumption.
Qed.

Proposition InclCompat : forall (A B:Class) (a b:U),
  a :<=: b                            ->
  (forall x, x :< a -> A!x :<=: B!x)  ->
  :\/:_{a} A  :<=: :\/:_{b} B.
Proof.
  intros A B a b H1 H2 y H3.
  apply Charac in H3. destruct H3 as [x [H3 H4]].
  apply Charac. exists x. split.
  - apply H1. assumption.
  - apply H2; assumption.
Qed.

Proposition InclCompatL : forall (A:Class) (a b:U),
  a :<=: b -> :\/:_{a} A :<=: :\/:_{b} A.
Proof.
  intros A B C H1. apply InclCompat. 1: assumption.
  intros x _. apply Incl.Refl.
Qed.

Proposition InclCompatR : forall (A B:Class) (a:U),
  (forall x, x :< a -> A!x :<=: B!x)  -> :\/:_{a} A :<=: :\/:_{a} B.
Proof.
  intros A B C H1. apply InclCompat. 2: assumption.
  apply Class.Incl.Refl.
Qed.

Proposition WhenBounded : forall (A:Class) (a b:U),
  (forall x, x :< a -> A!x :<=: b) -> :\/:_{a} A :<=: b.
Proof.
  intros A a b H1 y H2. apply Charac in H2. destruct H2 as [x [H2 H3]].
  apply (H1 x); assumption.
Qed.

