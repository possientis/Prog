Require Import ZF.Class.
Require Import ZF.Class.Incl.
Require Import ZF.Class.InitSegment.
Require Import ZF.Class.Minimal.
Require Import ZF.Set.
Require Import ZF.Set.Empty.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Singleton.

(* Predicate expressing the fact that R is a founded class on A.                *)
(* R is founded on A iff every non-empty subset of A has an R-minimal element.  *)
(* We wish this predicate to be expressed in the language of set theory, so     *)
(* while Coq allows us to quantify over all subclasses of A, we do not do so.   *)
Definition Founded (R A:Class) : Prop :=
  forall a, toClass a :<=: A /\ a <> :0: -> exists x, Minimal R (toClass a) x.

Proposition FoundedNoLoop1 : forall (R A:Class), Founded R A ->
  forall a, A a -> ~ R :(a,a):.
Proof.
  intros R A H1 a H2 H3.
  assert (exists x, Minimal R (toClass :{a}:) x) as H4. {
    apply H1. split.
    - apply SingleToClassIncl. assumption.
    - apply SingletonNotEmpty.
  } destruct H4 as [x [H4 H5]].
  apply SingleCharac in H4. subst.
  apply (InitSegmentEmptyInter1 _ _ _ a) in H5. 1: contradiction. apply SingleIn.
Qed.

Proposition FoundedNoLoop2 : forall (R A:Class), Founded R A ->
  forall a b, A a -> A b -> ~ (R :(a,b): /\ R :(b,a):).
Proof.
  intros R A H1 a b H2 H3 [H4 H5].
  assert (exists x, Minimal R (toClass :{a,b}:) x) as H6. {
    apply H1. split.
    - apply PairToClassIncl. split; assumption.
    - apply PairNotEmpty.
  } destruct H6 as [x [H6 H7]].
  apply PairCharac in H6. destruct H6 as [H6|H6]; subst.
  - apply (InitSegmentEmptyInter1 _ _ _ b) in H7. 1: contradiction. apply PairInR.
  - apply (InitSegmentEmptyInter1 _ _ _ a) in H7. 1: contradiction. apply PairInL.
Qed.

Proposition FoundedNoLoop3 : forall (R A:Class), Founded R A -> forall a1 a2 a3,
  A a1 ->
  A a2 ->
  A a3 ->
  ~ (R :(a1,a2): /\ R :(a2,a3): /\ R :(a3,a1):).
Proof.
Admitted.
