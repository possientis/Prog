Require Import ZF.Class.Core.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Single.
Require Import ZF.Set.Tuple.

(* Predicate expressing the fact that R is a founded class on A.                *)
(* R is founded on A iff every non-empty subset of A has an R-minimal element.  *)
(* We wish this predicate to be expressed in the language of set theory, so     *)
(* while Coq allows us to quantify over all subclasses of A, we do not do so.   *)
Definition Founded (R A:Class) : Prop := forall a,
  toClass a :<=: A ->
  a <> :0:         ->
  exists x, Minimal R (toClass a) x.

(* Convenient restating of the founded property in a small class context.       *)
Proposition WhenSmall : forall (R A B:Class),
  Founded R A ->
  Small B     ->
  B :<=: A    ->
  B :<>: :0:  ->
  exists x, Minimal R B x.
Proof.
  intros R A B H1 H2 H3 H4.
  apply Small.IsSomeSet in H2. destruct H2 as [b H2].
  assert (exists x, Minimal R (toClass b) x) as H5. {
    apply H1.
    - apply Incl.EquivCompatL with B; assumption.
    - apply NotEmptyToClass. apply NotEquivCompatL with B; assumption. }
  destruct H5 as [x H5]. exists x.
  apply Minimal.EquivCompatR with (toClass b). 2: assumption.
  apply EquivSym. assumption.
Qed.

(* If R is founded on A superclass of B, then it is founded on B.               *)
Proposition FoundedIncl : forall (R A B:Class),
  Founded R A -> B :<=: A -> Founded R B.
Proof.
  intros R A B H1 H2 a H3 H4. apply H1. 2: assumption.
  apply Class.Incl.Tran with B; assumption.
Qed.

Proposition FoundedIsom : forall (F R S A B:Class),
  Isom F R S A B -> Founded R A <-> Founded S B.
Proof.
  (* It is sufficient to prove -> *)
  assert (forall (F R S A B:Class),
    Isom F R S A B -> Founded R A -> Founded S B) as L. {
    intros F R S A B H1 H2 b H3 H4.
    remember (F^:-1::[toClass b]:) as C eqn:EC.
    assert (Small C) as H5. { rewrite EC.
      apply Bij.InvImageIsSmall with A B.
      - apply H1.
      - apply SetIsSmall. }
    remember (fromClass C H5) as a eqn:Ea. specialize (H2 a).
    assert (toClass a :~: F^:-1::[toClass b]:) as H6. {
      apply EquivTran with C.
      - rewrite Ea. apply ToFromClass.
      - rewrite <- EC. apply EquivRefl. }
    clear EC Ea H5 C.
    assert (toClass a :<=: A) as H7. {
      apply Incl.EquivCompatL with (F^:-1::[toClass b]:).
      - apply EquivSym. assumption.
      - apply Class.Incl.Tran with F^:-1::[B]:.
        + apply Image.InclCompatR. assumption.
        + apply Incl.EquivCompatL with A. 2: apply Class.Incl.Refl.
          apply EquivSym, Bij.InvImageOfRange, H1. }
    assert (a <> :0:) as H8. { apply HasElem in H4.
      destruct H4 as [y H4]. apply HasElem.
      exists F^:-1:!y. apply H6. exists y. split. 1: assumption.
      apply Bij.Satisfies with B A.
      - apply Bij.Converse, H1.
      - apply H3. assumption. }
    specialize (H2 H7 H8). destruct H2 as [x H2].
    assert (F:[toClass a]: :~: toClass b) as H9. {
      apply EquivTran with F:[F^:-1::[toClass b]:]:.
      - apply Image.EquivCompatR. assumption.
      - apply Bij.ImageOfInvImage with A B. 2: assumption. apply H1. }
    exists (F!x). apply Minimal.EquivCompatR with F:[toClass a]:.
    1: assumption. apply Minimal.IsomImage with R A B; try assumption.
    apply H7, Minimal.IsIn with R. assumption. }

  (* The proof of the equivalence follows. *)
  intros F R S A B H1. split.
  - apply L with F. assumption.
  - apply L with F^:-1:, Isom.Converse. assumption.
Qed.

Proposition FoundedNoLoop1 : forall (R A:Class), Founded R A ->
  forall a, A a -> ~ R :(a,a):.
Proof.
  intros R A H1 a H2 H3.
  assert (exists x, Minimal R (toClass :{a}:) x) as H4. {
    apply H1.
    - apply ToClassIncl. assumption.
    - apply SingletonIsNotEmpty.
  } destruct H4 as [x [H4 H5]].
  apply Single.Charac in H4. subst. revert H2.
  apply (InitSegment.WhenEmpty R (toClass :{a}:) a a) in H5.
  1: contradiction. apply Single.IsIn.
Qed.

Proposition FoundedNoLoop2 : forall (R A:Class), Founded R A ->
  forall a b, A a -> A b -> ~ (R :(a,b): /\ R :(b,a):).
Proof.
  intros R A H1 a b H2 H3 [H4 H5].
  assert (exists x, Minimal R (toClass :{a,b}:) x) as H6. {
    apply H1.
    - apply Pair.ToClassIncl. split; assumption.
    - apply PairIsNotEmpty.
  } destruct H6 as [x [H6 H7]].
  apply Pair.Charac in H6. destruct H6 as [H6|H6]; subst.
  - apply (InitSegment.WhenEmpty _ _ _ b) in H7. 1: contradiction. apply Pair.IsInR.
  - apply (InitSegment.WhenEmpty _ _ _ a) in H7. 1: contradiction. apply Pair.IsInL.
Qed.

Proposition FoundedNoLoop3 : forall (R A:Class), Founded R A -> forall a1 a2 a3,
  A a1 ->
  A a2 ->
  A a3 ->
  ~ (R :(a1,a2): /\ R :(a2,a3): /\ R :(a3,a1):).
Proof.
  intros R A H1 a1 a2 a3 H2 H3 H4 [H5 [H6 H7]].
  assert (exists x, Minimal R (toClass :{a1,a2,a3}:) x) as H8. {
  apply H1.
  - apply Tuple3ToClassIncl. split. 1: assumption. split; assumption.
  - apply Tuple3IsNotEmpty.
  } destruct H8 as [x [H8 H9]].
  apply Tuple3Charac in H8. destruct H8 as [H8|[H8|H8]]; subst.
  - apply (InitSegment.WhenEmpty _ _ _ a3) in H9. 1: contradiction. apply Tuple3In3.
  - apply (InitSegment.WhenEmpty _ _ _ a1) in H9. 1: contradiction. apply Tuple3In1.
  - apply (InitSegment.WhenEmpty _ _ _ a2) in H9. 1: contradiction. apply Tuple3In2.
Qed.

Proposition FoundedNoLoop4 : forall (R A:Class), Founded R A -> forall a1 a2 a3 a4,
  A a1 ->
  A a2 ->
  A a3 ->
  A a4 ->
  ~ (R :(a1,a2): /\ R :(a2,a3): /\ R :(a3,a4): /\ R :(a4,a1):).
Proof.
  intros R A H1 a1 a2 a3 a4 H2 H3 H4 H5 [H6 [H7 [H8 H9]]].
  assert (exists x, Minimal R (toClass :{a1,a2,a3,a4}:) x) as H10. {
  apply H1.
  - apply Tuple4ToClassIncl.
    split. 1: assumption.
    split. 1: assumption.
    split; assumption.
  - apply Tuple4IsNotEmpty.
  } destruct H10 as [x [H10 H11]].
  apply Tuple4Charac in H10. destruct H10 as [H10|[H10|[H10|H10]]]; subst.
  - apply (InitSegment.WhenEmpty _ _ _ a4) in H11. 1: contradiction. apply Tuple4In4.
  - apply (InitSegment.WhenEmpty _ _ _ a1) in H11. 1: contradiction. apply Tuple4In1.
  - apply (InitSegment.WhenEmpty _ _ _ a2) in H11. 1: contradiction. apply Tuple4In2.
  - apply (InitSegment.WhenEmpty _ _ _ a3) in H11. 1: contradiction. apply Tuple4In3.
Qed.
