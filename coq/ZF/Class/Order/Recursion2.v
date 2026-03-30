Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Closed.
Require Import ZF.Class.Order.Induction.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.Order.TranClosure.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Extend.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Single.
Require Import ZF.Set.Specify.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Image.

Module CIN := ZF.Class.Incl.
Module CRC := ZF.Class.Relation.Converse.
Module CRD := ZF.Class.Relation.Domain.
Module CRF := ZF.Class.Relation.Function.
Module CRL := ZF.Class.Relation.Functional.
Module CRR := ZF.Class.Relation.Relation.

(* Binary predicate underlying the recursion class.                             *)
Definition K (R A F:Class) : U -> U -> Prop := fun f a =>
  toClass a :<=: A                                                  /\
  Transitive R A a                                                  /\
  FunctionOn f a                                                    /\
  (forall b, b :< a-> f!b = F!(f:|:initSegment R A b)).

(* The recursion class associated with R A F. In other words, when R is well    *)
(* founded on A, the unique function class G defined on A by the recursion:     *)
(* G(b) = F(G|initSegment R A b).                                               *)
Definition Recursion (R A F:Class) : Class := fun x =>
  exists f a, x :< f /\ K R A F f a.

(* Two recursive functions coincide on their common domain.                     *)
Lemma Coincide : forall (R A F:Class) (f g a b x:U),
  WellFounded R A ->
  K R A F f a     ->
  K R A F g b     ->
  x :< a :/\: b   ->
  f!x = g!x.
Proof.
  intros R A F f g a b x H1 [H2 [H3 [H4 H5]]] [H6 [H7 [H8 H9]]] H10.
  assert (A :<=: A) as G1. { apply CIN.Refl. }
  apply Inter2.Charac in H10. destruct H10 as [H10 H11]. revert x H10 H11.
  remember (fun x => x :< a -> x :< b -> f!x = g!x) as B eqn:H12.
  assert (forall x, A x -> B x) as H13. {
    apply Induction.Induction with R. 1: assumption. rewrite H12.
    intros c H13 IH H14 H15.
    assert (initSegment R A c :<=: a) as H16. {
      apply TranClosure.InitSegment; assumption. }
    assert (initSegment R A c :<=: b) as H17. {
      apply TranClosure.InitSegment; assumption. }
    assert (forall x, x :< initSegment R A c -> f!x = g!x) as H18. {
      intros x H18. apply IH. 1: assumption.
      - apply H16. assumption.
      - apply H17. assumption. }
    assert (f:|:initSegment R A c = g :|: initSegment R A c) as H19. {
      apply FunctionOn.RestrictEqual with a b; assumption. }
    assert (f!c = F!(f:|:initSegment R A c)) as H20. { apply H5. assumption. }
    assert (g!c = F!(g:|:initSegment R A c)) as H21. { apply H9. assumption. }
    rewrite H20, H21, H19. reflexivity. }
    rewrite H12 in H13. intros x H14. apply H13. 2: assumption.
    apply H2. assumption.
Qed.

(* The recursion class associated with R A F is a relation class.               *)
Proposition IsRelation : forall (R A F:Class), CRR.Relation (Recursion R A F).
Proof.
  intros R A F x [f [a [H1 [H2 [H3 [H4 H5]]]]]]. apply H4. assumption.
Qed.

(* The restriction of a recursive function to transitive set is recursive.      *)
Lemma Restrict1 : forall (R A F:Class) (f a b:U),
  WellFounded R A   ->
  K R A F f a       ->
  b :<=: a          ->
  Transitive R A b  ->
  K R A F (f:|:b) b.
Proof.
  intros R A F f a b H1 [H2 [H3 [H4 H5]]] H6 H7. unfold K.
  assert (toClass b :<=: A) as H8. { intros x H8. apply H2, H6. assumption. }
  assert (FunctionOn (f:|:b) b) as H9. {
    apply FunctionOn.Restrict with a; assumption. }
  assert (
    forall x, x :< b -> (f:|:b)!x = F!((f:|:b) :|: initSegment R A x)) as H10. {
      intros c H10.
      assert (A :<=: A) as G1. { apply CIN.Refl. }
      assert (A c) as G2. { apply H8. assumption. }
      assert (f!c = F!(f:|:initSegment R A c)) as H11. {
        apply H5, H6. assumption. }
      assert ((f:|:b)!c = f!c) as H12. {
        apply Restrict.Eval. 2: assumption. apply H4. }
      assert (initSegment R A c :<=: b) as H13. {
        apply TranClosure.InitSegment; assumption. }
      assert ((f:|:b) :|: initSegment R A c = f:|:initSegment R A c) as H14. {
        apply Restrict.TowerProperty. assumption. }
      rewrite H12, H14. assumption. }
  split. 1: assumption. split. 1: assumption. split; assumption.
Qed.

(* The recursion class associated with R A F is a functional class.             *)
Proposition IsFunctional : forall (R A F:Class), WellFounded R A ->
  CRL.Functional (Recursion R A F).
Proof.
  intros R A F H1 x y1 y2 H2 H3.
  destruct H2 as [f1 [a1 [H2 H4]]].
  destruct H3 as [f2 [a2 [H3 H5]]].
  assert (domain f1 = a1) as H6. { apply H4. }
  assert (domain f2 = a2) as H7. { apply H5. }
  assert (x :< domain f1) as H8. { apply Domain.Charac. exists y1. assumption. }
  assert (x :< domain f2) as H9. { apply Domain.Charac. exists y2. assumption. }
  assert (x :< a1) as H10. {  rewrite <- H6. assumption. }
  assert (x :< a2) as H11. {  rewrite <- H7. assumption. }
  assert (f1!x = y1) as H12. { apply Eval.Charac; try assumption. apply H4. }
  assert (f2!x = y2) as H13. { apply Eval.Charac; try assumption. apply H5. }
  rewrite <- H12, <- H13.
  apply Coincide with R A F a1 a2; try assumption.
  apply Inter2.Charac. split; assumption.
Qed.

Proposition IsFunction : forall (R A F:Class), WellFounded R A ->
  CRF.Function (Recursion R A F).
Proof.
  intros R A F H1. split.
  - apply IsRelation.
  - apply IsFunctional. assumption.
Qed.

Lemma IsIncl1 : forall (R A F:Class),
  CRD.domain (Recursion R A F) :<=: A.
Proof.
  intros R A F x [y [f [a [H1 [H2 [H3 [H4 H5]]]]]]].
  assert (domain f = a) as H6. { apply H4. }
  assert (x :< a) as H7. {
    rewrite <- H6. apply Domain.Charac. exists y. assumption. }
  apply H2. assumption.
Qed.

Lemma Eval : forall (R A F:Class) (f a x:U),
  WellFounded R A                             ->
  toClass a :<=: CRD.domain (Recursion R A F) ->
  K R A F f a                                 ->
  x :< a                                      ->
  (Recursion R A F)!x = f!x.
Proof.
  intros R A F f a x H1 H2 H3 H4.
  apply CRF.EvalCharac.
  - apply IsFunction. assumption.
  - apply H2. assumption.
  - exists f, a. split. 2: assumption.
    apply FunctionOn.Satisfies with a. 2: assumption. apply H3.
Qed.

Lemma IsIncl2 : forall (R A F:Class) (f a:U),
  K R A F f a -> toClass a :<=: CRD.domain (Recursion R A F).
Proof.
  intros R A F f a H1 x H2. exists f!x, f, a. split. 2: assumption.
  apply FunctionOn.Satisfies with a. 2: assumption. apply H1.
Qed.

Lemma Recurse : forall (R A F:Class) (b:U),
  WellFounded R A                                                   ->
  CRD.domain (Recursion R A F) b                                    ->
  (Recursion R A F)!b = F!(Recursion R A F :|: initSegment R A b).
Proof.
  intros R A F b H1 [y [f [a [H2 H3]]]].
  assert (domain f = a) as G1. { apply H3. }
  assert (toClass a :<=: CRD.domain (Recursion R A F)) as G2. {
    apply IsIncl2 with f. assumption. }
  assert (b :< a) as G3. {
    rewrite <- G1. apply Domain.Charac. exists y. assumption. }
  assert ((Recursion R A F)!b = f!b) as H4. {
    apply Eval with a; try assumption. }
  assert (initSegment R A b :<=: a) as H5. {
    apply TranClosure.InitSegment; try apply H3; assumption. }
  assert (forall x, x :< initSegment R A b -> (Recursion R A F)!x = f!x) as H6. {
    intros x H6. apply Eval with a; try assumption. apply H5. assumption. }
  assert (toClass (initSegment R A b) :<=: CRD.domain (Recursion R A F)) as H7. {
    apply CIN.Tran with (toClass a); assumption. }
  assert (
    domain (Recursion R A F :|: initSegment R A b) = initSegment R A b) as H8. {
      apply RestrictOfClass.DomainWhenIncl. 2: assumption.
      apply IsFunctional. assumption. }
  assert (domain (f :|: initSegment R A b) = initSegment R A b) as H9. {
    apply Restrict.DomainWhenIncl. rewrite G1. assumption. }
  assert (Recursion R A F :|: initSegment R A b = f :|: initSegment R A b) as H10. {
    apply Function.EqualCharac.
    - apply RestrictOfClass.IsFunction, IsFunctional. assumption.
    - apply Function.Restrict, H3.
    - rewrite H8, H9. reflexivity.
    - intros x H10. rewrite H8 in H10.
      rewrite RestrictOfClass.Eval, Restrict.Eval; try assumption.
      + apply H6. assumption.
      + apply H3.
      + apply IsFunctional. assumption. }
  rewrite H4, H10. apply H3. assumption.
Qed.

Lemma Restrict2 : forall (R A F:Class) (a f:U),
  WellFounded R A                               ->
  toClass a :<=: CRD.domain (Recursion R A F)   ->
  Transitive R A a                              ->
  f = (Recursion R A F) :|: a                   ->
  K R A F f a.
Proof.
  intros R A F a f H1 H2 H3 H4. unfold K.
  assert (toClass a :<=: A) as H5. {
    apply CIN.Tran with (CRD.domain (Recursion R A F)). 1: assumption.
    apply IsIncl1. }
  assert (FunctionOn f a) as H6. {
    rewrite H4. apply RestrictOfClass.IsFunctionOn. 2: assumption.
    apply IsFunctional. assumption. }
  assert (forall b, b :< a -> f!b = F!(f :|: initSegment R A b)) as H7. {
    intros b H7.
    assert (initSegment R A b :<=: a) as H8. {
      apply TranClosure.InitSegment; assumption. }
    assert (CRD.domain (Recursion R A F) b) as H9. { apply H2. assumption. }
    assert (f!b = (Recursion R A F)!b) as H10. {
      rewrite H4. apply RestrictOfClass.Eval. 2: assumption.
      apply IsFunctional. assumption. }
    assert (f :|: initSegment R A b = Recursion R A F :|: initSegment R A b) as H11. {
      rewrite H4. apply RestrictOfClass.TowerProperty. 2: assumption.
      apply IsFunctional. assumption. }
      rewrite H10, H11. apply Recurse; assumption. }
  split. 1: assumption. split. 1: assumption. split; assumption.
Qed.

Lemma OnClosure : forall (R A F:Class) (a b f:U),
  WellFounded R A                                                         ->
  A a                                                                     ->
  (forall x,  x :< initSegment R A a -> CRD.domain (Recursion R A F) x)   ->
  b = closure R A (initSegment R A a)                                     ->
  f = (Recursion R A F) :|: b                                             ->
  K R A F f b.
Proof.
  intros R A F a b f H1 H2 H3 H4 H5.
  assert (A :<=: A) as G1. { apply CIN.Refl. }
  assert (toClass (initSegment R A a) :<=: A) as G2. {
    apply (InitSegment.IsIncl R A A); assumption. }

  assert (Transitive R A b) as H6. {
    rewrite H4. apply TranClosure.IsTransitive. 1: assumption.
    apply (InitSegment.IsIncl R A A); assumption. }
  assert (toClass b :<=: CRD.domain (Recursion R A F)) as H7. {
    remember ({{ x :< b | CRD.domain (Recursion R A F) }}) as c eqn:H8.
    assert (c :<=: b) as H9. { rewrite H8. apply Specify.IsInclL. }
    assert (toClass c :<=: A) as H10. {
      apply CIN.Tran with (toClass b). 1: assumption.
      rewrite H4. apply TranClosure.IsIncl; assumption. }
    assert (initSegment R A a :<=: c) as H11. {
      intros x H11. rewrite H8. apply Specify.Charac. split.
      - rewrite H4. apply TranClosure.Contains; assumption.
      - apply H3. assumption. }
    assert (Transitive R A c) as H12. {
      intros x y H12 H13 H14. rewrite H8 in H14.
      apply Specify.Charac in H14. destruct H14 as [H14 H15].
      rewrite H8. apply Specify.Charac. split.
      - revert H14. apply H6; assumption.
      - destruct H15 as [z [g [e [H15 H16]]]].
        apply (IsIncl2 R A F g e). 1: assumption.
        assert (domain g = e) as H17. { apply H16. }
        assert (y :< e) as H18. {
          rewrite <- H17. apply Domain.Charac. exists z. assumption. }
        assert (Transitive R A e) as H19. { apply H16. }
        revert H18. apply H19; assumption. }
    assert (b :<=: c) as H13. {
      rewrite H4. apply TranClosure.IsSmallest; assumption. }
    apply CIN.Tran with (toClass c). 1: assumption.
    rewrite H8. apply Specify.IsInclR. }
  apply Restrict2; assumption.
Qed.

Lemma Extend : forall (R A F:Class) (a b c f g:U),
  WellFounded R A                                   ->
  A a                                               ->
  b = closure R A (initSegment R A a)               ->
  c = b :\/: :{a}:                                  ->
  g = extend f a F!(f:|:initSegment R A a)          ->
  K R A F f b                                       ->
  K R A F g c.
Proof.
  intros R A F a b c f g H1 H2 H3 H4 H5 [H6 [H7 [H8 H9]]]. unfold K.
  assert (A :<=: A) as G1. { apply CIN.Refl. }
  assert (domain f = b) as G2. { apply H8. }
  assert (toClass c :<=: A) as H10. {
    intros x H10.
    rewrite H4 in H10. apply Union2.Charac in H10. destruct H10 as [H10|H10].
    - apply H6. assumption.
    - apply Single.Charac in H10. subst. assumption. }
  assert (Transitive R A c) as H11. {
    intros x y H11 H12 H13. rewrite H4 in H13. rewrite H4.
    apply Union2.Charac. left.
    apply Union2.Charac in H13. destruct H13 as [H13|H13].
    - revert H13. apply H7; assumption.
    - apply Single.Charac in H13. rewrite H13 in H12. rewrite H3.
      apply TranClosure.Contains. 1: assumption.
      + apply (InitSegment.IsIncl R A A); assumption.
      + apply (InitSegment.CharacRev R A A); assumption. }
  assert (~ a :< b) as H12. {
    rewrite H3. apply TranClosure.IsNotIn; assumption. }
  assert (~ a :< domain f) as G3. { rewrite G2. assumption. }
  assert (Functional f) as G4. { apply H8. }
  assert (FunctionOn g c) as H13. {
    rewrite H4, H5. apply Extend.IsFunctionOn; assumption. }
  assert (forall x, x :< c -> g!x = F!(g:|:initSegment R A x)) as H14. {
    intros x H14. rewrite H4 in H14. apply Union2.Charac in H14.
    destruct H14 as [H14|H14].
      assert (g!x = f!x) as K1. {
        rewrite H5. apply Extend.Evalf; try assumption.
        - rewrite G2. assumption. }
      assert (initSegment R A x :<=: b) as K2. {
        apply TranClosure.InitSegment; assumption. }
      assert (forall u, u :< initSegment R A x -> g!u = f!u) as K3. {
        intros u K3. rewrite H5. apply Extend.Evalf; try assumption.
        rewrite G2. apply K2. assumption. }
      assert (g:|:initSegment R A x = f:|:initSegment R A x) as K4. {
        apply FunctionOn.RestrictEqual with c b; try assumption.
        apply Incl.Tran with b. 1: assumption. rewrite H4.
        apply Union2.IsInclL. }
      rewrite K1, K4. apply H9. assumption.
    - apply Single.Charac in H14. rewrite H14.
      assert (g!a = F!(f:|:initSegment R A a)) as K1. {
        rewrite H5. apply Extend.Evalx; assumption. }
      assert (initSegment R A a :<=: b) as K2. {
        rewrite H3. apply TranClosure.Contains. 1: assumption.
        apply (InitSegment.IsIncl R A A); assumption. }
      assert (forall u, u :< initSegment R A a -> g!u = f!u) as K3. {
        intros u K3. rewrite H5. apply Extend.Evalf; try assumption.
        rewrite G2. apply K2. assumption. }
      assert (g:|:initSegment R A a = f:|:initSegment R A a) as K4. {
        apply FunctionOn.RestrictEqual with c b; try assumption.
        apply Incl.Tran with b. 1: assumption. rewrite H4.
        apply Union2.IsInclL. }
      rewrite K1, K4. reflexivity. }
  split. 1: assumption. split. 1: assumption. split; assumption.
Qed.

(*
Proposition DomainOf : forall (R A F:Class), WellFounded R A ->
  CRD.domain (Recursion R A F) :~: A.
Proof.
  intros R A F G1 x. split.
  - intros [y H1]. apply (proj1 (Charac2 R A F _ _)) in H1.
    destruct H1 as [f [a [H2 [H3 [H4 [H5 H6]]]]]].
    assert (domain f = a) as H7. { apply H5. }
    apply H3. rewrite <- H7. apply Domain.Charac. exists y. assumption.
  - revert x. apply Induction.Induction with R. 1: assumption.
    intros a H2 IH.
*)
(*
    remember (Recursion R A F :|: initSegment R A a) as f eqn:H8.
    assert (K R A F f (initSegment R A a)) as H9. {
      apply Restrict2; assumption. }
    remember (extend f a F!f) as g eqn:H10.
    remember (initSegment R A a :\/: :{a}:) as b eqn:H11.
    assert (K R A F g b) as H12. { apply Extend with a f; assumption. }
    exists F!f. apply Charac2. exists g, b. split. 2: assumption.
    rewrite H10. apply Union2.Charac. right. apply Single.IsIn.
Qed.
*)


