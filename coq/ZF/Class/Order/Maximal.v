Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.FinalSegment.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.ReflClosure.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

(* Predicate expressing the fact that a is an R-maximal element of A.           *)
Definition Maximal (R A:Class) (a:U) : Prop
  := A a /\ (forall x, A x -> ~ R :(a,x):).

Definition HasMaximal R A : Prop := exists a, Maximal R A a.

Definition HasNoMaximal R A : Prop := ~ HasMaximal R A.

Proposition EquivCompat : forall (R S A B:Class) (a:U),
  R :~: S -> A :~: B -> Maximal R A a -> Maximal S B a.
Proof.
  intros R S A B a H1 H2 [H3 H4]; split.
  - apply H2. assumption.
  - intros x H5 H6. apply H4 with x.
    + apply H2. assumption.
    + apply H1. assumption.
Qed.

Proposition EquivCompatL : forall (R S A:Class) (a:U),
  R :~: S -> Maximal R A a -> Maximal S A a.
Proof.
  intros R S A a H1. apply EquivCompat.
  - assumption.
  - apply Equiv.Refl.
Qed.

Proposition EquivCompatR : forall (R A B:Class) (a:U),
  A :~: B -> Maximal R A a -> Maximal R B a.
Proof.
  intros R A B a H1. apply EquivCompat.
  - apply Equiv.Refl.
  - assumption.
Qed.

Proposition IsIn : forall (R A:Class) (a:U),
  Maximal R A a -> A a.
Proof.
  intros R A a H1. apply H1.
Qed.

Proposition NotMore : forall (R A:Class) (a x:U),
  A x -> Maximal R A a -> ~ R :(a,x):.
Proof.
  intros R A a x H1 H2. apply H2. assumption.
Qed.

Proposition WhenHasNone : forall (R A:Class) (a:U),
  A a                           ->
  HasNoMaximal R A              ->
   exists b, A b /\ R :(a,b):.
Proof.
  intros R A a H1 H2. apply DoubleNegation. intros H3.
  apply H2. exists a. split. 1: assumption.
  intros b H4 H5. apply H3. exists b. split; assumption.
Qed.

Proposition IsomImage : forall (F R S A B C:Class) (a:U),
  Isom F R S A B          ->
  C :<=: A                ->
  A a                     ->
  Maximal R C a           ->
  Maximal S F:[C]: (F!a).
Proof.
  intros F R S A B C a H1 H2 H3 [H4 H5]. split.
  - apply (Bij.ImageCharac F A B). 1: apply H1.
    exists a. split. 1: assumption. split. 1: assumption. reflexivity.
  - intros y H6 H7. apply (Bij.ImageCharac F A B C) in H6. 2: apply H1.
    destruct H6 as [x [H6 [H8 H9]]]. rewrite <- H9 in H7.
    apply H1 in H7; try assumption. specialize (H5 x H6). contradiction.
Qed.

Proposition IsMinimal : forall (R A:Class) (a:U),
  Maximal R A a <-> Minimal R^:-1: A a.
Proof.
  intros R A a. split; intros H1.
  - split. 1: apply H1. intros x H2 H3. apply Converse.Charac2 in H3.
    destruct H1 as [H1 H4]. specialize (H4 x H2). contradiction.
  - split. 1: apply H1. intros x H2 H3. apply Converse.Charac2Rev in H3.
    destruct H1 as [H1 H4]. specialize (H4 x H2). contradiction.
Qed.

Proposition IsMaximal : forall (R A:Class) (a:U),
  Minimal R A a <-> Maximal R^:-1: A a.
Proof.
  intros R A a. split; intros H1.
  - split. 1: apply H1. intros x H2 H3. apply Converse.Charac2 in H3.
    destruct H1 as [H1 H4]. specialize (H4 x H2). contradiction.
  - split. 1: apply H1. intros x H2 H3. apply Converse.Charac2Rev in H3.
    destruct H1 as [H1 H4]. specialize (H4 x H2). contradiction.
Qed.


Proposition EmptySegment : forall (R A:Class) (a:U),
  Maximal R A a <-> A a /\ finalSegment R A a :~: :0:.
Proof.
  intros R A a. split; intros [H1 H2].
  - split. 1: assumption. apply FinalSegment.WhenEmptyRev. assumption.
  - split. 1: assumption. intros x. apply FinalSegment.WhenEmpty. assumption.
Qed.

Proposition InitRefl : forall (R A:Class) (a:U),
  Total R A                     ->
  Maximal R A a                 ->
  A :~: initSegment R^:=: A a.
Proof.
  intros R A a H1 H2. apply DoubleInclusion. split; intros x H3.
  - assert (x = a \/ R :(x,a): \/ R :(a,x):) as H4. {
      apply H1. 1: assumption. apply IsIn with R. assumption. }
    destruct H4 as [H4|[H4|H4]].
    + subst. apply InitSegment.IsInRefl. assumption.
    + apply InitSegment.CharacRefl. right.
      apply InitSegment.Charac. split; assumption.
    + exfalso. revert H4. apply H2. assumption.
  - apply InitSegment.IsIn with R^:=: a. assumption.
Qed.

(* If R is total on A the maximal element of a subclass of A is unique.         *)
Proposition Unique : forall (R A B:Class) (x y:U),
  Total R A       ->
  B :<=: A        ->
  Maximal R B x   ->
  Maximal R B y   ->
  x = y.
Proof.
  intros R A B x y H1 H2 H3 H4.
  apply Total.Converse in H1. apply IsMinimal in H3. apply IsMinimal in H4.
  apply Minimal.Unique with R^:-1: A B; assumption.
Qed.

