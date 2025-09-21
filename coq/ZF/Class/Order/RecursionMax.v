Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Maximal.
Require Import ZF.Class.Order.Recursion.
Require Import ZF.Class.Order.ReflClosure.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Module CIN := ZF.Class.Incl.
Module COI := ZF.Class.Order.InitSegment.
Module COR := ZF.Class.Order.Recursion.
Module CRD := ZF.Class.Relation.Domain.
Module CRF := ZF.Class.Relation.Function.
Module CFL := ZF.Class.Relation.Functional.
Module CFO := ZF.Class.Relation.FunctionOn.
Module CRR := ZF.Class.Relation.Relation.
Module SIN := ZF.Set.Incl.
Module SOI := ZF.Set.Order.InitSegment.
Module SFO := ZF.Set.Relation.FunctionOn.
Module SRD := ZF.Set.Relation.Domain.

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

(* The recursion class associated with R A F is a relation class.               *)
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

(* The recursion class associated with R A F is a function class.               *)
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

Lemma Coincide' : forall (R A F:Class) (a f:U),
  WellFoundedWellOrd R A                         ->
  Maximal R A a                                  ->
  f = COR.Recursion R A F :|: initSegment R A a  ->
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

Lemma Coincide : forall (R A F:Class) (a f:U),
  WellFoundedWellOrd R A                         ->
  Maximal R A a                                  ->
  f = Recursion R A F     :|: initSegment R A a  ->
  f = COR.Recursion R A F :|: initSegment R A a.
Proof.
  intros R A F a f H1 H2 H3.
  remember (COR.Recursion R A F :|: initSegment R A a) as g eqn:H4.
  symmetry. rewrite H3. apply Coincide'; assumption.
Qed.

Lemma AsSet : forall (R A F:Class) (a f g:U),
  WellFoundedWellOrd R A                      ->
  Maximal R A a                               ->
  f = Recursion R A F :|: initSegment R A a   ->
  g = f :\/: :{ :(a,F!f): }:                  ->
  toClass g :~: Recursion R A F.
Proof.
  intros R A F a f g H1 H2 H3 H4.
  assert (f = COR.Recursion R A F :|: initSegment R A a) as G1. {
    apply Coincide; assumption. }
  apply CIN.DoubleInclusion. split; intros x H5.
  - rewrite H4 in H5. apply Union2.Charac in H5. destruct H5 as [H5|H5].
    + apply (CharacRev R A F f a); try assumption. left. assumption.
    + apply (CharacRev R A F f a); try assumption. right.
      apply Single.Charac. assumption.
  - rewrite H4. apply (Charac R A F f a) in H5; try assumption.
    destruct H5 as [H5|H5]; apply Union2.Charac.
    + left. assumption.
    + right. apply Single.Charac. assumption.
Qed.

(* The recursion class associated with R A F is small.                          *)
Proposition IsSmall : forall (R A F:Class) (a:U),
  WellFoundedWellOrd R A    ->
  Maximal R A a             ->
  Small (Recursion R A F).
Proof.
  intros R A F a H1 H2.
  remember (Recursion R A F :|: initSegment R A a) as f eqn:H3.
  remember (f :\/: :{ :(a,F!f): }:) as g eqn:H4.
  exists g. apply (AsSet R A F a f g); assumption.
Qed.

Lemma Restrict : forall (R A F:Class) (a f:U),
  WellFoundedWellOrd R A                      ->
  Maximal R A a                               ->
  f = Recursion R A F :|: initSegment R A a   ->
  COR.K R A F f a.
Proof.
  intros R A F a f H1 H2 H3. apply COR.Restrict. 1: assumption.
  - apply Maximal.IsIn with R. assumption.
  - apply Coincide; assumption.
Qed.

Lemma Extend : forall (R A F:Class) (a f g:U),
  WellFoundedWellOrd R A                      ->
  Maximal R A a                               ->
  f = Recursion R A F :|: initSegment R A a   ->
  g = f :\/: :{ :(a,F!f): }:                  ->
  COR.KExt R A F g a.
Proof.
  intros R A F a f g H1 H2 H3 H4.
  apply (COR.Extend R A F a f g); try assumption. apply Restrict; assumption.
Qed.

(* The recursion class associated with R A F has domain A.                      *)
Proposition DomainIsA  : forall (R A F:Class) (a:U),
  WellFoundedWellOrd R A                ->
  Maximal R A a                         ->
  CRD.domain (Recursion R A F) :~: A.
Proof.
  intros R A F a H1 H2.
  assert (Total R A) as G1. { apply H1. }
  assert (WellFounded R A) as G2. { apply H1. }
  assert (A :<=: A) as G3. { apply Class.Incl.Refl. }
  assert (A a) as G4. { apply Maximal.IsIn with R. assumption. }
  remember (Recursion R A F :|: initSegment R A a) as f eqn:H3.
  remember (f :\/: :{ :(a,F!f): }:) as g eqn:H4.
  assert (COR.KExt R A F g a) as H5. { apply (Extend R A F a f g); assumption. }
  assert (toClass g :~: Recursion R A F) as H6. {
    apply (AsSet R A F a f g); assumption. }
  destruct H5 as [_ [[_ H5] _]]. apply CIN.DoubleInclusion. split; intros x H7.
  - apply (ReflClosure.WhenMax R A a); try assumption.
    apply (SOI.ToClassRefl R A A); try assumption. rewrite <- H5.
    destruct H7 as [y H7]. apply H6 in H7. apply SRD.Charac.
    exists y. assumption.
  - apply (ReflClosure.WhenMax R A a) in H7; try assumption.
    apply (SOI.ToClassRefl R A A) in H7; try assumption.
    rewrite <- H5 in H7. apply SRD.Charac in H7. destruct H7 as [y H7].
    exists y. apply H6. assumption.
Qed.

(* The recursion class associated with R A F is a function class defined on A.  *)
Proposition IsFunctionOn  : forall (R A F:Class) (a:U),
  WellFoundedWellOrd R A                ->
  Maximal R A a                         ->
  CFO.FunctionOn (Recursion R A F) A.
Proof.
  intros R A F a H1 H2. split.
  - apply IsFunction with a; assumption.
  - apply DomainIsA with a; assumption.
Qed.

(* The recursion class associated with R A F is F-recursive.                    *)
Proposition IsRecursive : forall (R A F:Class) (a b:U),
  WellFoundedWellOrd R A                                            ->
  Maximal R A a                                                     ->
  A b                                                               ->
  (Recursion R A F)!b = F!(Recursion R A F :|: initSegment R A b).
Proof.
  intros R A F a b H1 H2 H3.
  remember (Recursion R A F :|: initSegment R A a) as f eqn:H4.
  remember (f :\/: :{ :(a,F!f): }:) as g eqn:H5.
  assert (COR.KExt R A F g a) as H6. { apply (Extend R A F a f g); assumption. }
  assert (toClass g :~: Recursion R A F) as H7. {
    apply (AsSet R A F a f g); assumption. }
  destruct H6 as [H6 [H8 H9]].
  assert (forall x, A x -> (Recursion R A F)!x = g!x) as H10. {
    intros x H10. apply EvalOfClass.Charac.
    - apply IsFunction with a; assumption.
    - apply DomainIsA with a; assumption.
    - apply H7, SFO.Satisfies with (initSegment R^:=: A a). 1: assumption.
Admitted.
