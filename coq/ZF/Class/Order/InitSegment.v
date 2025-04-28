Require Import ZF.Class.Core.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Relation.InvImage.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Set.Core.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Single.

(* Inital segment of R on A at a.                                               *)
Definition initSegment (R A:Class) (a:U) : Class
  := A :/\: R^:-1: :[ toClass :{a}: ]:.

(* x belongs to initial segment iff it belongs to A and is 'less' than a.       *)
Proposition Charac : forall (R A:Class) (a x:U),
  initSegment R A a x <-> A x /\ R :(x,a):.
Proof.
  intros R A a x. split; intros [H1 H2].
  - split. 1: assumption. apply InvImage.Charac in H2. destruct H2 as [y [H2 H3]].
    apply Single.Charac in H2. subst. assumption.
  - split. 1: assumption. apply InvImage.Charac. exists a. split. 2: assumption.
    apply Single.IsIn.
Qed.

(* Initial segments are compatible with equivalences.                           *)
Proposition EquivCompat : forall (R S A B:Class) (a:U),
  R :~: S -> A :~: B -> initSegment R A a :~: initSegment S B a.
Proof.
  intros R S A B a H1 H2. apply Inter2.EquivCompat. 1: assumption.
  apply InvImage.EquivCompatL. assumption.
Qed.

(* Initial segments are left-compatible with equivalences.                      *)
Proposition EquivCompatL : forall (R S A:Class) (a:U),
  R :~: S -> initSegment R A a :~: initSegment S A a.
Proof.
  intros R S A a H1. apply EquivCompat.
  - assumption.
  - apply EquivRefl.
Qed.

(* Initial segments are right-compatible with equivalences.                     *)
Proposition EquivCompatR : forall (R A B:Class) (a:U),
  A :~: B -> initSegment R A a :~: initSegment R B a.
Proof.
  intros R A B a H1. apply EquivCompat.
  - apply EquivRefl.
  - assumption.
Qed.

(* Initial segments are compatible with inclusion.                              *)
Proposition InclCompat : forall (R S A B:Class) (a:U),
  R :<=: S -> A :<=: B -> initSegment R A a :<=: initSegment S B a.
Proof.
  intros R S A B a H1 H2. apply Inter2.InclCompat. 1: assumption.
  apply InvImage.InclCompatL. assumption.
Qed.

(* Initial segments are left-compatible with inclusion.                         *)
Proposition InclCompatL : forall (R S A:Class) (a:U),
  R :<=: S -> initSegment R A a :<=: initSegment S A a.
Proof.
  intros R S A a H1. apply InclCompat.
  - assumption.
  - apply InclRefl.
Qed.

(* Initial segments are right-compatible with inclusion.                        *)
Proposition InclCompatR : forall (R A B:Class) (a:U),
  A :<=: B -> initSegment R A a :<=: initSegment R B a.
Proof.
  intros R A B a H1. apply InclCompat.
  - apply InclRefl.
  - assumption.
Qed.

Proposition WhenIn : forall (R A:Class) (a x:U),
  initSegment R A a x -> A x.
Proof.
  intros R A a x H1. apply Charac in H1. apply H1.
Qed.

Proposition IsLess : forall (R A:Class) (a x:U),
  initSegment R A a x -> R :(x,a):.
Proof.
  intros R A a x H1. apply Charac in H1. apply H1.
Qed.

(* The initial segment is empty iff there is no x in A which is less than a.    *)
Proposition WhenEmpty : forall (R A:Class) (a x:U),
  initSegment R A a :~: :0: -> A x -> ~ R :(x,a):.
Proof.
  intros R A a x H1 H2 H3. apply Class.Empty.Charac with x. apply H1.
  apply Charac. split; assumption.
Qed.

Proposition WhenEmptyRev : forall (R A:Class) (a:U),
  (forall x, A x -> ~ R :(x,a):) -> initSegment R A a :~: :0:.
Proof.
  intros R A a H1 x. split; intros H2.
  + apply Charac in H2. destruct H2 as [H2 H3].
    apply Class.Empty.Charac. assert (H4 := H1 x H2). contradiction.
  + apply Class.Empty.Charac in H2. contradiction.
Qed.


(* Initial segments of R in A are subclasses of A.                              *)
Proposition IsIncl : forall (R A:Class) (a:U),
  initSegment R A a :<=: A.
Proof.
  intros R A a. apply Inter2.InclL.
Qed.

(* The direct image by an isomorphism of an inital segment is an inital segment.*)
Proposition IsomImage : forall (F R S A B C:Class) (a:U),
  Isom F R S A B    ->
  C :<=: A          ->
  A a               ->
  F:[initSegment R C a]: :~: initSegment S F:[C]: (F!a).
Proof.
  intros F R S A B C a [H1 H2] H3 H4 y. split; intros H5.
  - destruct H5 as [x [H5 H6]].
    apply Charac in H5. destruct H5 as [H5 H7].
    apply Charac. assert (F!x = y) as H8. {
      apply (Bij.EvalCharac F A B); try assumption. apply H3. assumption. }
    split.
    + exists x. split; assumption.
    + rewrite <- H8. apply H2; try assumption. apply H3. assumption.
  - apply Charac in H5. destruct H5 as [H5 H6].
    destruct H5 as [x [H5 H7]].
    assert (F!x = y) as H8. {
      apply (Bij.EvalCharac F A B); try assumption. apply H3. assumption. }
    exists x. split. 2: assumption.
    apply Charac. split. 1: assumption. apply H2. 2: assumption.
    + apply H3. assumption.
    + rewrite H8. assumption.
Qed.

Proposition IsomFullImage : forall (F R S A B:Class) (a:U),
  Isom F R S A B    ->
  A a               ->
  F:[initSegment R A a]: :~: initSegment S B (F!a).
Proof.
  intros F R S A B a H1 H2.
  apply EquivTran with (initSegment S F:[A]: F!a).
  - apply IsomImage with A B; try assumption. apply InclRefl.
  - apply EquivCompatR, Bij.ImageOfDomainIsRange, Isom.IsBij with R S.
    assumption.
Qed.

Proposition IsomWhenEmpty : forall (F R S A B C:Class) (a:U),
  Isom F R S A B                    ->
  C :<=: A                          ->
  A a                               ->
  initSegment R C a :~: :0:         ->
  initSegment S F:[C]: F!a :~: :0:.
Proof.
  intros F R S A B C a H1 H2 H3 H4.
  apply EquivTran with F:[initSegment R C a]:.
  - apply EquivSym, IsomImage with A B; assumption.
  - apply EmptyImage. assumption.
Qed.
