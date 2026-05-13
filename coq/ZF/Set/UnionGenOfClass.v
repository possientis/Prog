Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Fun.From.
Require Import ZF.Class.Small.
Require Import ZF.Class.UnionGen.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Relation.EvalOfClass.

Require Import ZF.Notation.UnionGen.
Export ZF.Notation.UnionGen.


Module CIN := ZF.Class.Incl.

(* The generalized union \/_{x :< a} A(x)                                       *)
Definition unionGen (a:U) (A:Class) : U := fromClass (:\/:_{toClass a} A)
  (UnionGen.IsSmall (toClass a) A (SetIsSmall a)).

(* Notation ":\/:_{ a } A" := (unionGen a A)                                    *)
Global Instance SetUnionGenOfClass : UnionGen U Class := {unionGen := unionGen }.

(* y belongs to the generalized union iff y belongs to some A(x) with x in a.   *)
Proposition Charac : forall (A:Class) (a y:U),
  y :< :\/:_{a} A <-> exists x, x :< a /\ y :< A!x.
Proof.
  intros A a y. split; intros H1.
  - apply FromClass.Charac in H1. apply UnionGen.Charac in H1. assumption.
  - apply FromClass.Charac, UnionGen.Charac. assumption.
Qed.

(* The generalized union is the same when classes A and B agree on a.           *)
Proposition Equal : forall (A B:Class) (a:U),
  (forall x, x :< a -> A!x = B!x) -> :\/:_{a} A = :\/:_{a} B.
Proof.
  intros a A B H1. apply Incl.Double. split; intros y H2;
  apply Charac in H2; destruct H2 as [x [H2 H3]]; apply Charac;
  exists x; split; try assumption.
  - rewrite <- H1; assumption.
  - rewrite H1; assumption.
Qed.

(* The generalized union is invariant under class equivalence of the family.    *)
Proposition EquivCompat : forall (A B:Class) (a:U),
  A :~: B -> :\/:_{a} A = :\/:_{a} B.
Proof.
  intros A B a H1.
  apply Equal. intros x H2.
  apply EvalOfClass.EquivCompat. assumption.
Qed.

(* If x is in a, then A(x) is included in the generalized union over a.         *)
Proposition IsIncl : forall (A:Class) (a x:U),
  x :< a -> A!x :<=: :\/:_{a} A.
Proof.
  intros A a x H1 y H2. apply Charac. exists x. split; assumption.
Qed.

(* The generalized union is monotone in both the index set and the family.      *)
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

(* The generalized union is monotone in the left index set.                     *)
Proposition InclCompatL : forall (A:Class) (a b:U),
  a :<=: b -> :\/:_{a} A :<=: :\/:_{b} A.
Proof.
  intros A B C H1. apply InclCompat. 1: assumption.
  intros x _. apply Incl.Refl.
Qed.

(* The generalized union is monotone in the right family.                       *)
Proposition InclCompatR : forall (A B:Class) (a:U),
  (forall x, x :< a -> A!x :<=: B!x)  -> :\/:_{a} A :<=: :\/:_{a} B.
Proof.
  intros A B C H1. apply InclCompat. 2: assumption.
  apply CIN.Refl.
Qed.

(* If each A(x) is a subset of b for x in a, the generalized union is too.      *)
Proposition WhenSetBounded : forall (A:Class) (a b:U),
  (forall x, x :< a -> A!x :<=: b) -> :\/:_{a} A :<=: b.
Proof.
  intros A a b H1 y H2. apply Charac in H2. destruct H2 as [x [H2 H3]].
  apply (H1 x); assumption.
Qed.

(* If each A(x) is a subclass of B for x in a, so is the generalized union.     *)
Proposition WhenClassBounded : forall (A B:Class) (a:U),
  (forall x, x :< a -> toClass A!x :<=: B) -> toClass (:\/:_{a} A) :<=: B.
Proof.
  intros A B a H1 y H2. apply Charac in H2. destruct H2 as [x [H2 H3]].
  apply (H1 x); assumption.
Qed.

(* The generalized union is unchanged by eta-reducing the family.               *)
Proposition EtaReduce : forall (A:Class) (a:U),
  :\/:_{a} :[fun x => A!x]: = :\/:_{a} A.
Proof.
  intros A a. apply Equal. intros x H1. apply From.Eval.
Qed.

