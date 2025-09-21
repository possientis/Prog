Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.FinalSegment.
Require Import ZF.Class.Order.Maximal.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.ReflClosure.
Require Import ZF.Class.Order.Succ.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.Transitive.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Truncate.

Module COS := ZF.Class.Order.Succ.
Module CIN := ZF.Class.Incl.
Module SIN := ZF.Set.Incl.

(* The successor in the ordered class (A,R) of a set a.                         *)
Definition succ (R A:Class) (a:U) : U := truncate (COS.succ R A a).

Proposition ToClass : forall (R A:Class) (a:U),
  WellFoundedWellOrd R A                    ->
  A a                                       ->
  toClass (succ R A a) :~: COS.succ R A a.
Proof.
  intros R A a H1 H2.
  apply Truncate.WhenSmall, COS.IsSmall; assumption.
Qed.

Proposition Charac : forall (R A:Class) (a b:U),
  WellFoundedWellOrd R A                        ->
  A a                                           ->
  ~ Maximal R A a                               ->
  succ R A a = b                               <->
  A b                                           /\
  R :(a,b):                                     /\
  forall x, A x -> R :(a,x): -> ~ R :(x,b):.
Proof.
  intros R A a b H1 H2 H3. split; intros H4.
  - apply COS.WhenNotMaximal in H3; try assumption.
    destruct H3 as [c [H3 [H5 [H6 H7]]]].
    assert (c = b) as H8. {
      rewrite <- H4. apply EqualToClass.
      apply Equiv.Tran with (COS.succ R A a). 1: assumption.
      apply Equiv.Sym, ToClass; assumption. }
    rewrite <- H8. split. 1: assumption. split; assumption.
  - apply COS.WhenNotMaximal in H3; try assumption.
    destruct H3 as [c [H3 [H5 [H6 H7]]]].
    destruct H4 as [H4 [H8 H9]].
    remember (finalSegment R A a) as B eqn:H10.
    assert (Minimal R B b) as H11. {
      split.
      - rewrite H10. apply FinalSegment.Charac. split; assumption.
      - intros x H11. rewrite H10 in H11. apply FinalSegment.Charac in H11.
        destruct H11 as [H11 H12]. apply H9; assumption. }
    assert (Minimal R B c) as H12. {
      split.
      - rewrite H10. apply FinalSegment.Charac. split; assumption.
      - intros x H12. rewrite H10 in H12. apply FinalSegment.Charac in H12.
        destruct H12 as [H12 H13]. apply H7; assumption. }
    assert (B :<=: A) as H13. { rewrite H10. apply FinalSegment.IsIncl. }
    assert (Total R A) as H14. { apply H1. }
    assert (c = b) as H15. { apply (Minimal.Unique R A B); assumption. }
    subst. symmetry. apply EqualToClass.
    apply Equiv.Tran with (COS.succ R A a). 1: assumption.
    apply Equiv.Sym, ToClass; assumption.
Qed.

(* The successor of a belongs to the class A.                                   *)
Proposition IsIn : forall (R A:Class) (a:U),
  WellFoundedWellOrd R A  ->
  A a                     ->
  ~ Maximal R A a         ->
  A (succ R A a).
Proof.
  intros R A a H1 H2 H3.
  apply (Charac R A a (succ R A a)) in H3; try assumption.
  destruct H3 as [H3 _]. specialize (H3 eq_refl). apply H3.
Qed.

(* The successor of a is greater than a.                                        *)
Proposition IsMore : forall (R A:Class) (a:U),
  WellFoundedWellOrd R A  ->
  A a                     ->
  ~ Maximal R A a         ->
  R :(a,succ R A a):.
Proof.
  intros R A a H1 H2 H3.
  apply (Charac R A a (succ R A a)) in H3; try assumption.
  destruct H3 as [H3 _]. specialize (H3 eq_refl). apply H3.
Qed.

(* The successor of a belongs to the final segment (a<).                        *)
Proposition IsInSegment : forall (R A:Class) (a:U),
  WellFoundedWellOrd R A            ->
  A a                               ->
  ~ Maximal R A a                   ->
  finalSegment R A a (succ R A a).
Proof.
  intros R A a H1 H2 H3. apply FinalSegment.Charac. split.
  - apply IsIn; assumption.
  - apply IsMore; assumption.
Qed.

(* The successor of a is an R-minimal element of (a<).                          *)
Proposition IsMinimal : forall (R A:Class) (a:U),
  WellFoundedWellOrd R A                        ->
  A a                                           ->
  ~ Maximal R A a                               ->
  Minimal R (finalSegment R A a) (succ R A a).
Proof.
  intros R A a H1 H2 H3. assert (H4 := H3).
  apply (Charac R A a (succ R A a)) in H3; try assumption.
  destruct H3 as [H3 _]. specialize (H3 eq_refl).
  destruct H3 as [H3 [H5 H6]]. split.
  - apply IsInSegment; assumption.
  - intros x H7. apply FinalSegment.Charac in H7. apply H6; apply H7.
Qed.

(* A set x in A which is more than a, cannot be less than the successor of a.   *)
Proposition IsNotLess : forall (R A:Class) (a x:U),
  WellFoundedWellOrd R A                        ->
  A a                                           ->
  ~ Maximal R A a                               ->
  A x                                           ->
  R :(a,x):                                     ->
  ~ R :(x,succ R A a):.
Proof.
  intros R A a x H1 H2 H3 H4 H5.
  apply (Charac R A a (succ R A a)) in H3; try assumption.
  destruct H3 as [H3 _]. specialize (H3 eq_refl).
  destruct H3 as [H3 [H6 H7]]. apply H7; assumption.
Qed.

(* The initial segment at a is a subset of the initial segment at (succ a).     *)
Proposition IsIncl : forall (R A:Class) (a:U),
  WellFoundedWellOrd R A                                ->
  A a                                                   ->
  ~ Maximal R A a                                       ->
  initSegment R A a :<=: initSegment R A (succ R A a).
Proof.
  intros R A  a H1 H2 H3 x H4.
  assert (Transitive R A) as H5. {
    apply WellFoundedWellOrd.IsTransitive. assumption. }
  assert (WellFounded R A) as H6. { apply H1. }
  assert (A :<=: A) as H7. { apply CIN.Refl. }
  apply (InitSegment.Charac R A A) in H4; try assumption. destruct H4 as [H4 H8].
  apply (InitSegment.CharacRev R A A); try assumption.
  - apply IsIn; assumption.
  - apply H5 with a; try assumption.
    + apply IsIn; assumption.
    + apply IsMore; assumption.
Qed.

Proposition InInit: forall (R A:Class) (a:U),
  WellFoundedWellOrd R A                                ->
  A a                                                   ->
  ~ Maximal R A a                                       ->
  a :< initSegment R A (succ R A a).
Proof.
  intros R A a H1 H2 H3.
  assert (WellFounded R A) as H4. { apply H1. }
  assert (A :<=: A) as H5. { apply CIN.Refl. }
  apply (InitSegment.CharacRev R A A); try assumption.
  - apply IsIn; assumption.
  - apply IsMore; assumption.
Qed.

(* The R-initial segment at (succ a) is the R^=-initial segment at a.           *)
Proposition InitRefl : forall (R A:Class) (a:U),
  WellFoundedWellOrd R A                                ->
  A a                                                   ->
  ~ Maximal R A a                                       ->
  initSegment R A (succ R A a) = initSegment R^:=: A a.
Proof.
  intros R A a H1 H2 H3. apply SIN.DoubleInclusion.
  assert (WellFounded R A) as H4. { apply H1. }
  assert (Total R A) as H5. { apply H1. }
  assert (A :<=: A) as H6. { apply CIN.Refl. }
  split; intros x H7.
  - apply (InitSegment.Charac R A A) in H7; try assumption.
    2: apply IsIn; try assumption. destruct H7 as [H7 H8].
    apply (InitSegment.CharacRefl R A A); try assumption.
    assert (x = a \/ R :(x,a): \/ R :(a,x):) as H9. { apply H5; assumption. }
    destruct H9 as [H9|[H9|H9]].
    + left. split; assumption.
    + right. apply InitSegment.CharacRev with A; assumption.
    + exfalso. apply (IsNotLess R A a x) in H3; try assumption. contradiction.
  - apply (InitSegment.CharacRefl R A A) in H7; try assumption.
    destruct H7 as [[H7 H8]|H7].
    + subst. apply InitSegment.CharacRev with A; try assumption.
      * apply IsIn; assumption.
      * apply IsMore; assumption.
    + apply IsIncl; assumption.
Qed.

