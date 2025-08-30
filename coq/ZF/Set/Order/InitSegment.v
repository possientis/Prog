Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.
Require Import ZF.Set.Truncate.

Module COI := ZF.Class.Order.InitSegment.

(* Initial segment of R on A at a.                                              *)
Definition initSegment (R A:Class) (a:U) : U := truncate (COI.initSegment R A a).

Proposition ToClass : forall (R A B:Class) (a:U),
  WellFounded R A                                         ->
  A a                                                     ->
  B :<=: A                                                ->
  toClass (initSegment R B a) :~: COI.initSegment R B a.
Proof.
  intros R A B a H1 H2 H3.
  apply Truncate.WhenSmall, WellFounded.IsSmall with A; assumption.
Qed.

Proposition Charac : forall (R A B:Class) (a x:U),
  WellFounded R A         ->
  A a                     ->
  B :<=: A                ->
  x :< initSegment R B a  ->
  B x /\ R :(x,a):.
Proof.
  intros R A B a x H1 H2 H3 H4.
  apply (ToClass R A B a) in H4; try assumption.
  apply COI.Charac in H4. assumption.
Qed.

Proposition CharacRev : forall (R A B:Class) (a x:U),
  WellFounded R A           ->
  A a                       ->
  B :<=: A                  ->
  B x                       ->
  R :(x,a):                 ->
  x :< initSegment R B a.
Proof.
  intros R A B a x H1 H2 H3 H4 H5.
  apply (ToClass R A B a); try assumption. apply COI.Charac. split; assumption.
Qed.

(* Initial segments are compatible with equivalences.                           *)
Proposition EquivCompat : forall (R S A B:Class) (a:U),
  R :~: S -> A :~: B -> initSegment R A a = initSegment S B a.
Proof.
  intros R S A B a H1 H2.
  apply Truncate.EquivCompat, COI.EquivCompat; assumption.
Qed.

(* Initial segments are left-compatible with equivalences.                      *)
Proposition EquivCompatL : forall (R S A:Class) (a:U),
  R :~: S -> initSegment R A a = initSegment S A a.
Proof.
  intros R S A a H1. apply EquivCompat.
  - apply H1.
  - apply Equiv.Refl.
Qed.

(* Initial segments are right-compatible with equivalences.                     *)
Proposition EquivCompatR : forall (R A B:Class) (a:U),
  A :~: B -> initSegment R A a = initSegment R B a.
Proof.
  intros R A B a H1. apply EquivCompat.
  - apply Equiv.Refl.
  - apply H1.
Qed.


Proposition WhenIn : forall (R A B:Class) (a x:U),
  WellFounded R A         ->
  A a                     ->
  B :<=: A                ->
  x :< initSegment R B a  ->
  B x.
Proof.
  intros R A B a x H1 H2 H3 H4.
  apply (Charac R A B a); assumption.
Qed.

Proposition IsLess : forall (R A B:Class) (a x:U),
  WellFounded R A         ->
  A a                     ->
  B :<=: A                ->
  x :< initSegment R B a  ->
  R :(x,a):.
Proof.
  intros R A B a x H1 H2 H3 H4.
  apply (Charac R A B a) in H4; try assumption. apply H4.
Qed.

(* The initial segment is empty iff there is no x in A which is less than a.    *)
Proposition WhenEmpty : forall (R A B:Class) (a x:U),
  WellFounded R A         ->
  A a                     ->
  B :<=: A                ->
  initSegment R B a = :0: ->
  B x                     ->
  ~ R :(x,a):.
Proof.
  intros R A B a x H1 H2 H3 H4 H5 H6. apply Empty.Charac with x.
  rewrite <- H4. apply CharacRev with A; try assumption.
Qed.

Proposition WhenEmptyRev : forall (R A B:Class) (a:U),
  WellFounded R A                 ->
  A a                             ->
  B :<=: A                        ->
  (forall x, B x -> ~ R :(x,a):)  ->
  initSegment R B a = :0:.
Proof.
  intros R A B a H1 H2 H3 H4. apply DoubleInclusion. split; intros x H5.
  - exfalso. apply (Charac R A B a) in H5; try assumption.
    destruct H5 as [H5 H6]. specialize (H4 x H5). contradiction.
  - apply Empty.Charac in H5. contradiction.
Qed.

Proposition IsIncl : forall (R A B:Class) (a:U),
  WellFounded R A                     ->
  A a                                 ->
  B :<=: A                            ->
  toClass (initSegment R B a) :<=: B.
Proof.
  intros R A B a H1 H2 H3 x H4. apply (WhenIn R A B a); assumption.
Qed.

(* The direct image by an isomorphism of an inital segment is an inital segment.*)
Proposition IsomImage : forall (F R S A B C:Class) (a:U),
  WellFounded R A                                       ->
  A a                                                   ->
  C :<=: A                                              ->
  Isom F R S A B                                        ->
  F:[initSegment R C a]: = initSegment S F:[C]: F!a.
Proof.
  intros F R S A B C a H1 H2 H3 H4.
  assert (WellFounded S B) as H5. {
    apply (WellFounded.WhenIsom F R S A B); assumption. }
  assert (B (F!a)) as H6. {
    apply Bij.IsInRange with A. 2: assumption. apply H4. }
  assert (F:[C]: :<=: B) as H7. {
    apply (Bij.ImageIncl F A B). 2: assumption. apply H4. }
  apply DoubleInclusion. split; intros y H8.
  - apply ImageByClass.Charac in H8. 2: apply H4. destruct H8 as [x [H8 H9]].
    apply (Charac R A C a) in H8; try assumption. destruct H8 as [H8 H10].
    apply (CharacRev S B F:[C]: F!a); try assumption.
    + exists x. split; assumption.
    + assert (F!x = y) as H11. {
        apply (Bij.EvalCharac F A B). 3: assumption.
        - apply H4.
        - apply H3. assumption. }
      rewrite <- H11. apply H4; try assumption. apply H3. assumption.
  - apply (Charac S B F:[C]: F!a) in H8; try assumption.
    destruct H8 as [[x [H8 H9]] H10].
    assert (F!x = y) as H11. {
      apply (Bij.EvalCharac F A B). 3: assumption.
      - apply H4.
      - apply H3. assumption. }
    rewrite <- H11 in H10. apply H4 in H10. 3: assumption.
    2: { apply H3. assumption. }
    apply ImageByClass.CharacRev with x. 3: assumption.
    + apply H4.
    + apply (CharacRev R A C a); assumption.
Qed.

Proposition IsomFullImage : forall (F R S A B:Class) (a:U),
  WellFounded R A                                         ->
  A a                                                     ->
  Isom F R S A B                                          ->
  F:[initSegment R A a]: = initSegment S B F!a.
Proof.
  intros F R S A B a H1 H2 H3.
  assert (F:[A]: :~: B) as H4. { apply Bij.ImageOfDomain, H3. }
  assert (initSegment S F:[A]: (F!a) = initSegment S B (F!a)) as H5. {
    apply EquivCompatR. assumption. }
  rewrite <- H5. apply IsomImage with A B; try assumption.
  apply Class.Incl.Refl.
Qed.

Proposition IsomWhenEmpty : forall (F R S A B C:Class) (a:U),
  WellFounded R A                   ->
  A a                               ->
  C :<=: A                          ->
  Isom F R S A B                    ->
  initSegment R C a = :0:           ->
  initSegment S F:[C]: F!a = :0:.
Proof.
  intros F R S A B C a H1 H2 H3 H4 H5.
  rewrite <- (IsomImage F R S A B C); try assumption.
  apply ImageByClass.WhenEmpty. assumption.
Qed.
