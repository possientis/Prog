Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.Founded.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Irreflexive.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.StrictOrd.
Require Import ZF.Class.Order.StrictTotalOrd.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.Transitive.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Single.
Require Import ZF.Set.Tuple.

(* Predicate expressing the fact that R is a well-ordering class on A.          *)
(* R is a well-ordering on A iff it is founded on A and total on A.             *)
Definition WellOrdering (R A:Class) : Prop :=  Founded R A /\ Total R A.

Proposition WhenIncl : forall (R A B:Class),
  WellOrdering R A -> B :<=: A -> WellOrdering R B.
Proof.
  intros R A B [H1 H2] H3. split.
  - apply FoundedIncl with A; assumption.
  - apply TotalIncl with A; assumption.
Qed.

Proposition IsIrreflexive : forall (R A:Class),
  WellOrdering R A -> Irreflexive R A.
Proof.
  intros R A [H1 H2] a H3.
  assert (exists x, Minimal R (toClass :{a}:) x) as H4. {
    apply H1.
    - apply ToClassIncl. assumption.
    - apply SingletonIsNotEmpty.
  } destruct H4 as [x H4]. assert (H5 := H4). apply Minimal.IsIn in H5.
  apply Single.Charac in H5. subst.
  apply Minimal.NotLess with (toClass :{a}:). 2: assumption. apply Single.IsIn.
Qed.

Proposition IsTransitive : forall (R A:Class),
  WellOrdering R A -> Transitive R A.
Proof.
  intros R A [H1 H2] x y z H3 H4 H5 H6 H7.
  specialize (H2 x z H3 H5). destruct H2 as [H2|[H2|H2]].
  - subst. exfalso. assert (R :(y,z): /\ R :(z,y):) as H8. { split; assumption. }
    revert H8. apply (FoundedNoLoop2 R A H1 y z); assumption.
  - assumption.
  - exfalso. assert (exists u, Minimal R (toClass :{x,y,z}:) u) as H8. {
      apply H1.
      - apply Tuple3ToClassIncl. split. 1: assumption. split; assumption.
      - apply Tuple3IsNotEmpty.
    } destruct H8 as [u H8]. assert (H9 := H8). apply Minimal.IsIn in H9.
    apply Tuple3Charac in H9. destruct H9 as [H9|[H9|H9]]; subst.
    + assert (~R :(z,x):) as H9. {
        apply Minimal.NotLess with (toClass :{x,y,z}:).
        2: assumption. apply Tuple3In3.
      } contradiction.

    + assert (~R :(x,y):) as H9. {
        apply Minimal.NotLess with (toClass :{x,y,z}:).
        2: assumption. apply Tuple3In1.
      } contradiction.

    + assert (~R :(y,z):) as H9. {
        apply Minimal.NotLess with (toClass :{x,y,z}:).
        2: assumption. apply Tuple3In2.
      } contradiction.
Qed.

Proposition IsStrictOrd : forall (R A:Class),
  WellOrdering R A -> StrictOrd R A.
Proof.
  intros R A H1. split.
  - apply IsIrreflexive. assumption.
  - apply IsTransitive. assumption.
Qed.

Proposition IsStrictTotalOrd :  forall (R A:Class),
  WellOrdering R A -> StrictTotalOrd R A.
Proof.
  intros R A H1. split.
  - apply IsStrictOrd. assumption.
  - apply H1.
Qed.

Proposition WhenLess : forall (R A:Class) (x y:U),
  A x                ->
  A y                ->
  WellOrdering R A   ->
  R :(x,y):         <->
  ~ (x = y \/ R :(y,x): ).
Proof.
  intros R A x y H1 H2 H3. apply StrictTotalOrdWhenLess with A.
  - assumption.
  - assumption.
  - apply IsStrictTotalOrd. assumption.
Qed.

Proposition IsNotIn : forall (R A:Class) (a:U),
  WellOrdering R A -> ~ initSegment R A a a.
Proof.
  intros R A a H1 H2. assert (H3 := H2). apply InitSegment.IsLess in H2.
  apply IsIrreflexive in H1. specialize (H1 a).
  apply InitSegment.IsIn in H3. apply H1; assumption.
Qed.

Proposition WhenIsom : forall (F R S A B:Class),
  Isom F R S A B -> WellOrdering R A <-> WellOrdering S B.
Proof.
  intros F R S A B H1. split; intros [H2 H3]; split.
  - apply (FoundedIsom F R S A B); assumption.
  - apply (TotalIsom F R S A B); assumption.
  - apply (FoundedIsom F R S A B); assumption.
  - apply (TotalIsom F R S A B); assumption.
Qed.

Proposition NotInImage : forall (F R S A B:Class) (a:U),
  WellOrdering S B ->
  Isom F R S A B   ->
  A a              ->
  ~ F:[initSegment R A a]: (F!a).
Proof.
  intros F R S A B a H1 H2 H3 H4. apply (IsNotIn R A a).
  - apply (WhenIsom F R S A B); assumption.
  - apply (Bij.EvalInImage F A B); try assumption. apply H2.
Qed.
