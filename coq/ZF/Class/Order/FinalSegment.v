Require Import ZF.Class.Equiv.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Transitive.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Single.

(* Inital segment of R on A at a.                                               *)
Definition finalSegment (R A:Class) (a:U) : Class
  := A :/\: R :[ toClass :{a}: ]:.

(* x belongs to final segment iff it belongs to A and is 'more' than a.         *)
Proposition Charac : forall (R A:Class) (a x:U),
  finalSegment R A a x <-> A x /\ R :(a,x):.
Proof.
  intros R A a x. split; intros [H1 H2].
  - split. 1: assumption. destruct H2 as [y [H2 H3]].
    apply Single.Charac in H2. subst. assumption.
  - split. 1: assumption. exists a. split. 2: assumption. apply Single.IsIn.
Qed.

Proposition InInit : forall (R A:Class) (a x:U),
  finalSegment R A a x <-> initSegment R^:-1: A a x.
Proof.
  intros R A a x. split; intros H1.
  - apply Charac in H1. destruct H1 as [H1 H2]. apply InitSegment.Charac.
    split. 1: assumption. apply Converse.Charac2Rev. assumption.
  - apply InitSegment.Charac in H1. destruct H1 as [H1 H2].
    apply Converse.Charac2 in H2. apply Charac. split; assumption.
Qed.

(* Final segments are compatible with equivalences.                             *)
Proposition EquivCompat : forall (R S A B:Class) (a:U),
  R :~: S -> A :~: B -> finalSegment R A a :~: finalSegment S B a.
Proof.
  intros R S A B a H1 H2. apply Inter2.EquivCompat. 1: assumption.
  apply Image.EquivCompatL. assumption.
Qed.

(* Final segments are left-compatible with equivalences.                        *)
Proposition EquivCompatL : forall (R S A:Class) (a:U),
  R :~: S -> finalSegment R A a :~: finalSegment S A a.
Proof.
  intros R S A a H1. apply EquivCompat.
  - assumption.
  - apply Equiv.Refl.
Qed.

(* Final segments are right-compatible with equivalences.                       *)
Proposition EquivCompatR : forall (R A B:Class) (a:U),
  A :~: B -> finalSegment R A a :~: finalSegment R B a.
Proof.
  intros R A B a H1. apply EquivCompat.
  - apply Equiv.Refl.
  - assumption.
Qed.

(* Final segments are compatible with inclusion.                                *)
Proposition InclCompat : forall (R S A B:Class) (a:U),
  R :<=: S -> A :<=: B -> finalSegment R A a :<=: finalSegment S B a.
Proof.
  intros R S A B a H1 H2. apply Class.Inter2.InclCompat. 1: assumption.
  apply Image.InclCompatL. assumption.
Qed.

(* Final segments are left-compatible with inclusion.                           *)
Proposition InclCompatL : forall (R S A:Class) (a:U),
  R :<=: S -> finalSegment R A a :<=: finalSegment S A a.
Proof.
  intros R S A a H1. apply InclCompat.
  - assumption.
  - apply Class.Incl.Refl.
Qed.

(* Final segments are right-compatible with inclusion.                          *)
Proposition InclCompatR : forall (R A B:Class) (a:U),
  A :<=: B -> finalSegment R A a :<=: finalSegment R B a.
Proof.
  intros R A B a H1. apply InclCompat.
  - apply Class.Incl.Refl.
  - assumption.
Qed.


Proposition WhenIn : forall (R A:Class) (a x:U),
  finalSegment R A a x -> A x.
Proof.
  intros R A a x H1. apply Charac in H1. apply H1.
Qed.


Proposition IsMore : forall (R A:Class) (a x:U),
  finalSegment R A a x -> R :(a,x):.
Proof.
  intros R A a x H1. apply Charac in H1. apply H1.
Qed.

(* The final segment is empty iff there is no x in A which is more than a.      *)
Proposition WhenEmpty : forall (R A:Class) (a x:U),
  finalSegment R A a :~: :0: -> A x -> ~ R :(a,x):.
Proof.
  intros R A a x H1 H2 H3. apply Class.Empty.Charac with x. apply H1.
  apply Charac. split; assumption.
Qed.

Proposition WhenEmptyRev : forall (R A:Class) (a:U),
  (forall x, A x -> ~ R :(a,x):) -> finalSegment R A a :~: :0:.
Proof.
  intros R A a H1 x. split; intros H2.
  + apply Charac in H2. destruct H2 as [H2 H3].
    apply Class.Empty.Charac. assert (H4 := H1 x H2). contradiction.
  + apply Class.Empty.Charac in H2. contradiction.
Qed.

(* Final segments of R in A are subclasses of A.                                *)
Proposition IsIncl : forall (R A:Class) (a:U),
  finalSegment R A a :<=: A.
Proof.
  intros R A a. apply Class.Inter2.IsInclL.
Qed.

Proposition WhenMore : forall (R A:Class) (a b:U),
  Transitive R A                            ->
  A a                                       ->
  A b                                       ->
  R :(b,a):                                 ->
  finalSegment R A a :<=: finalSegment R A b.
Proof.
  intros R A a b H1 H2 H3 H4 x H5.
  apply Charac in H5. destruct H5 as [H5 H6].
  apply Charac. split. 1: assumption. apply H1 with a; assumption.
Qed.

(* The direct image by an isomorphism of an final segment is an final segment.  *)
Proposition IsomImage : forall (F R S A B C:Class) (a:U),
  Isom F R S A B                                          ->
  C :<=: A                                                ->
  A a                                                     ->
  F:[finalSegment R C a]: :~: finalSegment S F:[C]: (F!a).
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
    apply Charac. split. 1: assumption. apply H2. 1: assumption.
    + apply H3. assumption.
    + rewrite H8. assumption.
Qed.

Proposition IsomFullImage : forall (F R S A B:Class) (a:U),
  Isom F R S A B    ->
  A a               ->
  F:[finalSegment R A a]: :~: finalSegment S B F!a.
Proof.
  intros F R S A B a H1 H2.
  apply Equiv.Tran with (finalSegment S F:[A]: F!a).
  - apply IsomImage with A B; try assumption. apply Class.Incl.Refl.
  - apply EquivCompatR, Bij.ImageOfDomain, H1.
Qed.

Proposition IsomWhenEmpty : forall (F R S A B C:Class) (a:U),
  Isom F R S A B                      ->
  C :<=: A                            ->
  A a                                 ->
  finalSegment R C a :~: :0:          ->
  finalSegment S F:[C]: F!a :~: :0:.
Proof.
  intros F R S A B C a H1 H2 H3 H4.
  apply Equiv.Tran with F:[finalSegment R C a]:.
  - apply Equiv.Sym, IsomImage with A B; assumption.
  - apply Empty.ImageOf. assumption.
Qed.

