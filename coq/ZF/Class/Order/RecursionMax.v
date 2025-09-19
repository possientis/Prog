Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.Maximal.
Require Import ZF.Class.Order.Recursion.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Module COR := ZF.Class.Order.Recursion.
Module CRF := ZF.Class.Relation.Function.
Module CRR := ZF.Class.Relation.Relation.
Module SIN := ZF.Set.Incl.

(* The recursion class associated with R A F. In other words, when R is a well  *)
(* founded well ordering on A and A has a maximal element, the unique function  *)
(* class G defined on A by the recursion G(b) = F(G|initSegment R A b).         *)
Definition Recursion (R A F:Class) : Class := fun x => exists f a,
    Maximal R A a                                                   /\
    f = COR.Recursion R A F :|: initSegment R A a                   /\
    x :< f :\/: :{ :(a,F!f): }:.

Proposition Charac : forall (R A F:Class) (f a x:U),
  WellFoundedWellOrd R A                              ->
  Maximal R A a                                       ->
  f = COR.Recursion R A F :|: initSegment R A a       ->
  Recursion R A F x                                   ->
  x :< f \/ x = :(a,F!f):.
Proof.
  intros R A F f a x H1 H2 H3 H4. destruct H4 as [g [b [H4 [H5 H6]]]].
  assert (a = b) as H7. {
    apply Total.MaxUnique with R A A; try assumption. 1: apply H1.
    apply Class.Incl.Refl. }
  assert (f = g) as H8. { rewrite H7 in H3. rewrite <- H5 in H3. assumption. }
  apply Union2.Charac in H6. destruct H6 as [H6|H6].
  - left. rewrite H8. assumption.
  - right. rewrite H7,H8. apply Single.Charac. assumption.
Qed.

Proposition CharacRev : forall (R A F:Class) (f a x:U),
  WellFoundedWellOrd R A                              ->
  Maximal R A a                                       ->
  f = COR.Recursion R A F :|: initSegment R A a       ->
  x :< f \/ x = :(a,F!f):                             ->
  Recursion R A F x.
Proof.
  intros R A F f a x H1 H2 H3 H4. exists f. exists a.
  split. 1: assumption. split. 1: assumption.
  apply Union2.Charac. destruct H4 as [H4|H4].
  - left. assumption.
  - right. apply Single.Charac. assumption.
Qed.

Proposition Charac2 : forall (R A F:Class) (f a x y:U),
  WellFoundedWellOrd R A                                  ->
  Maximal R A a                                           ->
  f = COR.Recursion R A F :|: initSegment R A a           ->
  Recursion R A F :(x,y):                                 ->
  :(x,y): :< f \/ x = a /\ y = F!f.
Proof.
  intros R A F f a x y H1 H2 H3 H4.
  apply (Charac _ _ _ f a) in H4; try assumption. destruct H4 as [H4|H4].
  - left. assumption.
  - right. apply OrdPair.WhenEqual in H4. destruct H4 as [H4 H5].
    split; assumption.
Qed.

Proposition Charac2Rev : forall (R A F:Class) (f a x y:U),
  WellFoundedWellOrd R A                                  ->
  Maximal R A a                                           ->
  f = COR.Recursion R A F :|: initSegment R A a           ->
  :(x,y): :< f \/ x = a /\ y = F!f                        ->
  Recursion R A F :(x,y):.
Proof.
  intros R A F f a x y H1 H2 H3 H4.
  apply (CharacRev _ _ _ f a); try assumption. destruct H4 as [H4|H4].
  - left. assumption.
  - right. destruct H4 as [H4 H5]. rewrite H4, H5. reflexivity.
Qed.

Proposition IsRelation : forall (R A F:Class) (a:U),
  WellFoundedWellOrd R A              ->
  Maximal R A a                       ->
  CRR.Relation (Recursion R A F).
Proof.
  intros R A F a H1 H2 x H3.
  remember (COR.Recursion R A F :|: initSegment R A a) as f eqn:H4.
  apply (Charac R A F f a) in H3; try assumption. destruct H3 as [H3|H3].
  - rewrite H4 in H3. apply RestrictOfClass.Charac in H3.
    + destruct H3 as [y [z [H3]]]. exists y. exists z. assumption.
    + apply COR.IsFunction. assumption.
  - exists a. exists F!f. assumption.
Qed.

Proposition IsFunction : forall (R A F:Class) (a:U),
  WellFoundedWellOrd R A              ->
  Maximal R A a                       ->
  CRF.Function (Recursion R A F).
Proof.
  intros R A F a H1 H2. split.
  - apply IsRelation with a; assumption.
  - intros x y z H3 H4.
    assert (WellFounded R A) as G1. { apply H1. }
    assert (A :<=: A) as G2. { apply Class.Incl.Refl. }
    assert (A a) as G3. { apply Maximal.IsIn with R. assumption. }
    remember (COR.Recursion R A F :|: initSegment R A a) as f eqn:H5.
    apply (Charac R A F f a) in H3; try assumption.
    apply (Charac R A F f a) in H4; try assumption.
    destruct H3 as [H3|H3]; destruct H4 as [H4|H4].
    + rewrite H5 in H3. apply RestrictOfClass.Charac2 in H3.
      2: { apply COR.IsFunction. assumption. } destruct H3 as [_ H3].
      rewrite H5 in H4. apply RestrictOfClass.Charac2 in H4.
      2: { apply COR.IsFunction. assumption. } destruct H4 as [_ H4].
      revert H3 H4. apply COR.IsFunction. assumption.
    + rewrite H5 in H3. apply RestrictOfClass.Charac2 in H3.
      2: { apply COR.IsFunction. assumption. } destruct H3 as [H3 _].
      apply OrdPair.WhenEqual in H4. destruct H4 as [H4 H6].
      rewrite H4 in H3. exfalso.
      apply (InitSegment.IsLess R A A) in H3; try assumption.
      revert H3. apply H2. assumption.
    + rewrite H5 in H4. apply RestrictOfClass.Charac2 in H4.
      2: { apply COR.IsFunction. assumption. } destruct H4 as [H4 _].
      apply OrdPair.WhenEqual in H3. destruct H3 as [H3 H6].
      rewrite H3 in H4. exfalso.
      apply (InitSegment.IsLess R A A) in H4; try assumption.
      revert H4. apply H2. assumption.
    + apply OrdPair.WhenEqual in H3. destruct H3 as [_ H3].
      apply OrdPair.WhenEqual in H4. destruct H4 as [_ H4].
      rewrite H4. assumption.
Qed.

Lemma Coincide : forall (R A F:Class) (a f:U),
  WellFoundedWellOrd R A                                  ->
  Maximal R A a                                           ->
  f = COR.Recursion R A F :|: initSegment R A a           ->
  f = Recursion R A F     :|: initSegment R A a.
Proof.
  intros R A F a f H1 H2 H3.
  assert (WellFounded R A) as G1. { apply H1. }
  assert (A :<=: A) as G2. { apply Class.Incl.Refl. }
  assert (A a) as G3. { apply Maximal.IsIn with R. assumption. }
  apply SIN.DoubleInclusion. split; intros x H4.
  - assert (G4 := H4). rewrite H3 in H4. apply RestrictOfClass.Charac in H4.
    2: { apply COR.IsFunction. assumption. }
    destruct H4 as [y [z [H4 [H5 H6]]]].
    apply RestrictOfClass.CharacRev with y z; try assumption.
    + apply (IsFunction R A F a); assumption.
    + apply (CharacRev R A F f a); try assumption. left.
      rewrite H4 in G4. assumption.
  - apply RestrictOfClass.Charac in H4.
    2: { apply (IsFunction R A F a); assumption. }
    destruct H4 as [y [z [H4 [H5 H6]]]].
    apply (Charac2 R A F f a) in H6; try assumption. destruct H6 as [H6|H6].
    + rewrite H4. assumption.
    + exfalso. destruct H6 as [H6 _]. rewrite H6 in H5.
      apply (InitSegment.IsLess R A A) in H5; try assumption.
      revert H5. apply H2. assumption.
Qed.

