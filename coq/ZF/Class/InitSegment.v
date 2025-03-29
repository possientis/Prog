Require Import ZF.Class.
Require Import ZF.Class.Bij.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.InvImage.
Require Import ZF.Class.Isom.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Singleton.

(* Inital segment of R on A at a.                                               *)
Definition initSegment (R A:Class) (a:U) : Class
  := A :/\: R^:-1: :[ toClass :{a}: ]:.

(* x belongs to initial segment iff it belongs to A and is 'less' than a.       *)
Proposition InitSegmentCharac : forall (R A:Class) (a x:U),
  initSegment R A a x <-> A x /\ R :(x,a):.
Proof.
  intros R A a x. split; intros [H1 H2].
  - split. 1: assumption. apply InvImageCharac in H2. destruct H2 as [y [H2 H3]].
    apply SingleCharac in H2. subst. assumption.
  - split. 1: assumption. apply InvImageCharac. exists a. split. 2: assumption.
    apply SingleIn.
Qed.

(* Initial segments are compatible with equivalences.                           *)
Proposition InitSegmentEquivCompat : forall (R S A B:Class) (a:U),
  R :~: S -> A :~: B -> initSegment R A a :~: initSegment S B a.
Proof.
  intros R S A B a H1 H2. apply Inter.EquivCompat. 1: assumption.
  apply InvImageEquivCompatL. assumption.
Qed.

(* Initial segments are left-compatible with equivalences.                      *)
Proposition InitSegmentEquivCompatL : forall (R S A:Class) (a:U),
  R :~: S -> initSegment R A a :~: initSegment S A a.
Proof.
  intros R S A a H1. apply InitSegmentEquivCompat.
  - assumption.
  - apply ClassEquivRefl.
Qed.

(* Initial segments are right-compatible with equivalences.                     *)
Proposition InitSegmentEquivCompatR : forall (R A B:Class) (a:U),
  A :~: B -> initSegment R A a :~: initSegment R B a.
Proof.
  intros R A B a H1. apply InitSegmentEquivCompat.
  - apply ClassEquivRefl.
  - assumption.
Qed.

(* Initial segments are compatible with inclusion.                              *)
Proposition InitSegmentInclCompat : forall (R S A B:Class) (a:U),
  R :<=: S -> A :<=: B -> initSegment R A a :<=: initSegment S B a.
Proof.
  intros R S A B a H1 H2. apply Inter.InclCompat. 1: assumption.
  apply InvImageInclCompatL. assumption.
Qed.

(* Initial segments are left-compatible with inclusion.                         *)
Proposition InitSegmentInclCompatL : forall (R S A:Class) (a:U),
  R :<=: S -> initSegment R A a :<=: initSegment S A a.
Proof.
  intros R S A a H1. apply InitSegmentInclCompat.
  - assumption.
  - apply InclRefl.
Qed.

(* Initial segments are right-compatible with inclusion.                        *)
Proposition InitSegmentInclCompatR : forall (R A B:Class) (a:U),
  A :<=: B -> initSegment R A a :<=: initSegment R B a.
Proof.
  intros R A B a H1. apply InitSegmentInclCompat.
  - apply InclRefl.
  - assumption.
Qed.

Proposition InitSegmentIn : forall (R A:Class) (a x:U),
  initSegment R A a x -> A x.
Proof.
  intros R A a x H1. apply InitSegmentCharac in H1. apply H1.
Qed.

Proposition InitSegmentLess : forall (R A:Class) (a x:U),
  initSegment R A a x -> R :(x,a):.
Proof.
  intros R A a x H1. apply InitSegmentCharac in H1. apply H1.
Qed.

(* The initial segment is empty iff there is no x in A which is less than a.    *)
Proposition InitSegmentWhenEmpty : forall (R A:Class) (a:U),
  initSegment R A a :~: :0: <-> forall x, A x -> ~ R :(x,a):.
Proof.
  intros R A a. split; intros H1.
  - intros x H2 H3. apply Empty.Charac with x. apply H1.
    apply InitSegmentCharac. split; assumption.
  - intros x. split; intros H2.
    + apply InitSegmentCharac in H2. destruct H2 as [H2 H3].
      apply Empty.Charac. assert (H4 := H1 x H2). contradiction.
    + apply Empty.Charac in H2. contradiction.
Qed.

(* If x lies in A and the initial segment is empty, then it is not less than a. *)
Proposition InitSegmentWhenEmpty1 : forall (R A:Class) (a x:U),
  A x -> initSegment R A a :~: :0: -> ~ R :(x,a):.
Proof.
  intros R A a x H1 H2.
  assert (H3 := proj1 (InitSegmentWhenEmpty R A a) H2 x H1). assumption.
Qed.

(* Initial segments of R in A are subclasses of A.                              *)
Proposition InitSegmentIncl : forall (R A:Class) (a:U),
  initSegment R A a :<=: A.
Proof.
  intros R A a. apply Inter.InclL.
Qed.

(* The direct image by an isomorphism of an inital segment is an inital segment.*)
Proposition InitSegmentIsomImage : forall (F R S A B C:Class) (a:U),
  Isom F R S A B    ->
  C :<=: A          ->
  A a               ->
  F:[initSegment R C a]: :~: initSegment S F:[C]: (F!a).
Proof.
  intros F R S A B C a [H1 H2] H3 H4 y. split; intros H5.
  - destruct H5 as [x [H5 H6]].
    apply InitSegmentCharac in H5. destruct H5 as [H5 H7].
    apply InitSegmentCharac. assert (F!x = y) as H8. {
      apply (Bij.EvalCharac F A B); try assumption. apply H3. assumption. }
    split.
    + exists x. split; assumption.
    + rewrite <- H8. apply H2; try assumption. apply H3. assumption.
  - apply InitSegmentCharac in H5. destruct H5 as [H5 H6].
    destruct H5 as [x [H5 H7]].
    assert (F!x = y) as H8. {
      apply (Bij.EvalCharac F A B); try assumption. apply H3. assumption. }
    exists x. split. 2: assumption.
    apply InitSegmentCharac. split. 1: assumption. apply H2. 2: assumption.
    + apply H3. assumption.
    + rewrite H8. assumption.
Qed.

Proposition InitSegmentIsomFullImage : forall (F R S A B:Class) (a:U),
  Isom F R S A B    ->
  A a               ->
  F:[initSegment R A a]: :~: initSegment S B (F!a).
Proof.
  intros F R S A B a H1 H2.
  apply ClassEquivTran with (initSegment S F:[A]: F!a).
  - apply InitSegmentIsomImage with A B; try assumption. apply InclRefl.
  - apply InitSegmentEquivCompatR, Bij.ImageOfDomainIsRange, Isom.IsBij with R S.
    assumption.
Qed.

Proposition InitSegmentIsomWhenEmpty : forall (F R S A B C:Class) (a:U),
  Isom F R S A B                    ->
  C :<=: A                          ->
  A a                               ->
  initSegment R C a :~: :0:         ->
  initSegment S F:[C]: F!a :~: :0:.
Proof.
  intros F R S A B C a H1 H2 H3 H4.
  apply ClassEquivTran with F:[initSegment R C a]:.
  - apply ClassEquivSym, InitSegmentIsomImage with A B; assumption.
  - apply EmptyImage. assumption.
Qed.
