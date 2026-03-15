Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Closed.
Require Import ZF.Class.Order.Induction.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.Order.InitSegment.
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
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Image.

Module CIN := ZF.Class.Incl.
Module CRC := ZF.Class.Relation.Converse.
Module CRF := ZF.Class.Relation.Function.
Module CRL := ZF.Class.Relation.Functional.
Module CRR := ZF.Class.Relation.Relation.


(* The recursion class associated with R A F. In other words, when R is well    *)
(* founded on A, the unique function class G defined on A by the recursion:     *)
(* G(b) = F(G|initSegment R A b).                                               *)
Definition Recursion (R A F:Class) : Class := fun x => exists f a,
  x :< f                                                            /\
  toClass a :<=: A                                                  /\
  Closed R^:-1: (toClass a)                                         /\
  FunctionOn f a                                                    /\
  (forall b, b :< a -> f!b = F!(f:|:initSegment R A b)).

(* Binary predicate underlying the recursion class.                             *)
Definition K (R A F:Class) : U -> U -> Prop := fun f a =>
  toClass a :<=: A                                                  /\
  Closed R^:-1: (toClass a)                                         /\
  FunctionOn f a                                                    /\
  (forall b, b :< a-> f!b = F!(f:|:initSegment R A b)).

Proposition Charac2 : forall (R A F:Class) (x y:U),
  Recursion R A F :(x,y): <-> exists f a, :(x,y): :< f /\ K R A F f a.
Proof.
  intros R A F x y. split; intros [f [a [H1 H2]]];
  exists f, a; split; assumption.
Qed.

(* Two recursive functions coincide on their common domain.                     *)
Lemma Coincide : forall (R A F:Class) (f g a b:U),
  WellFounded R A                                         ->
  toClass a :<=: A                                        ->
  Closed R^:-1: (toClass a)                               ->
  a :<=: b                                                ->
  FunctionOn f a                                          ->
  FunctionOn g b                                          ->
  (forall x, x :< a -> f!x = F!(f:|:initSegment R A x))   ->
  (forall x, x :< b -> g!x = F!(g:|:initSegment R A x))   ->
  (forall x, x :< a -> f!x = g!x).
Proof.
  intros R A F f g a b H1 H2 H4 H6 H7 H8 H9 H10.
  assert (A :<=: A) as G1. { apply CIN.Refl. }
  remember (fun x => x :< a -> f!x = g!x) as B eqn:H12.
  assert (forall x, A x -> B x) as H13. {
    apply Induction.Induction with R. 1: assumption. rewrite H12.
    intros c H13 IH H14.
    assert (initSegment R A c :<=: a) as H15. {
      intros u H15.
      assert (R :(u,c):) as H16. {
        apply (InitSegment.IsLess R A A); assumption. }
      apply H4. exists c. split. 1: assumption.
      apply CRC.Charac2Rev. assumption. }
    assert (initSegment R A c :<=: b) as H16. {
      apply Incl.Tran with a; assumption. }
    assert (forall x, x :< initSegment R A c -> f!x = g!x) as H17. {
      intros x H17. apply IH. 1: assumption. apply H15. assumption. }
    assert (f:|:initSegment R A c = g :|: initSegment R A c) as H18. {
      apply FunctionOn.RestrictEqual with a b; assumption. }
    assert (f!c = F!(f:|:initSegment R A c)) as H19. {
      apply H9. assumption. }
    assert (g!c = F!(g:|:initSegment R A c)) as H20. {
      apply H10, H6. assumption. }
    rewrite H19, H20, H18. reflexivity. }
    rewrite H12 in H13. intros x H14. apply H13. 2: assumption.
    apply H2. assumption.
Qed.

(* The recursion class associated with R A F is a relation class.               *)
Proposition IsRelation : forall (R A F:Class), CRR.Relation (Recursion R A F).
Proof.
  intros R A F x [f [a [H1 [H2 [H3 [H4 H5]]]]]]. apply H4. assumption.
Qed.

Lemma Restrict1 : forall (R A F:Class) (f g a b:U),
  WellFounded R A                                         ->
  toClass a :<=: A                                        ->
  Closed R^:-1: (toClass a)                               ->
  a :<=: b                                                ->
  FunctionOn f b                                          ->
  g = f:|:a                                               ->
  (forall x, x :< b -> f!x = F!(f:|:initSegment R A x))   ->
  (forall x, x :< a -> g!x = F!(g:|:initSegment R A x)).
Proof.
  intros R A F f g a b H1 H2 H3 H4 H5 H6 H7 c H8.
  assert (A :<=: A) as G1. { apply CIN.Refl. }
  assert (A c) as G2. { apply H2. assumption. }
  assert (f!c = F!(f:|:initSegment R A c)) as H9. { apply H7, H4. assumption. }
  assert (g!c = f!c) as H10. {
    rewrite H6. apply Restrict.Eval. 2: assumption. apply H5. }
  assert (initSegment R A c :<=: a) as H11. {
    intros x H11. apply H3. exists c. split. 1: assumption.
    apply CRC.Charac2Rev, (InitSegment.IsLess R A A); assumption. }
  assert (g:|:initSegment R A c = f:|:initSegment R A c) as H12. {
    rewrite H6. apply Restrict.TowerProperty. assumption. }
    rewrite H12, H10. assumption.
Qed.

(* The recursion class associated with R A F is a functional class.             *)
Proposition IsFunctional : forall (R A F:Class), WellFounded R A ->
  CRL.Functional (Recursion R A F).
Proof.
  intros R A F G1 x y1 y2 H1 H2.
  destruct H1 as [f1 [a1 [H3 [H4 [H5 [H6 H7]]]]]].
  destruct H2 as [f2 [a2 [H8 [H9 [H10 [H11 H12]]]]]].
  remember (a1 :/\: a2) as a eqn:G2.
  remember (f1:|:a) as f eqn:G3.
  assert (toClass a :<=: A) as H14. {
    intros u H14. rewrite G2 in H14. apply Inter2.Charac in H14.
    apply H4, H14. }
  assert (Closed R^:-1: (toClass a)) as H15. {
    intros u [v [H15 H16]]. rewrite G2 in H15.
    apply Inter2.Charac in H15. destruct H15 as [H15 H17].
    rewrite G2. apply Inter2.Charac. split.
    - apply H5. exists v. split; assumption.
    - apply H10. exists v. split; assumption. }
  assert (a :<=: a1) as H16. { rewrite G2. apply Inter2.IsInclL. }
  assert (a :<=: a2) as H17. { rewrite G2. apply Inter2.IsInclR. }
  assert (FunctionOn f a) as H18. {
    rewrite G3. apply FunctionOn.Restrict with a1; assumption. }
  assert (forall x, x :< a -> f!x = F!(f:|:initSegment R A x)) as H19. {
    apply Restrict1 with f1 a1; assumption. }
  assert (forall u, u :< a -> f!u = f1!u) as H20. {
    apply Coincide with R A F a1; assumption. }
  assert (forall u, u :< a -> f!u = f2!u) as H21. {
    apply Coincide with R A F a2; assumption. }
  assert (x :< domain f1) as H22. {
    apply Domain.Charac. exists y1. assumption. }
  assert (x :< domain f2) as H23. {
    apply Domain.Charac. exists y2. assumption. }
  assert (domain f1 = a1) as H24. { apply H6. }
  assert (domain f2 = a2) as H25. { apply H11. }
  assert (x :< a) as H26. {
    rewrite G2, <- H24, <- H25. apply Inter2.Charac. split; assumption. }
  assert (f1!x = y1) as H27. { apply Eval.Charac; try assumption. apply H6. }
  assert (f2!x = y2) as H28. { apply Eval.Charac; try assumption. apply H11. }
  rewrite <- H27, <- H28, <- H20, <- H21; try assumption. reflexivity.
Qed.

Proposition IsFunction : forall (R A F:Class), WellFounded R A ->
  CRF.Function (Recursion R A F).
Proof.
  intros R A F H1. split.
  - apply IsRelation.
  - apply IsFunctional. assumption.
Qed.


Lemma Restrict2 : forall (R A F:Class) (a f:U),
  WellFounded R A                                                         ->
  A a                                                                     ->
  (forall x,  x :< initSegment R A a -> CRD.domain (Recursion R A F) x)   ->
  f = (Recursion R A F) :|: initSegment R A a                             ->
  K R A F f (initSegment R A a).
Proof.
  intros R A F a f H1 H2 H3 H4. unfold K.
  assert (A :<=: A) as G1. { apply CIN.Refl. }
  assert (toClass (initSegment R A a) :<=: A) as H5. {
    intros x H5. apply (InitSegment.IsIn R A A) with a; assumption. }
  assert (Closed R^:-1: (toClass (initSegment R A a))) as H6. {
    intros y [x [H6 H7]]. apply CRC.Charac2 in H7.
    apply InitSegment.CharacRev with A.
Admitted.

(*
Lemma Extend : forall (R A F:Class) (a b f g:U),
  WellFounded R A                   ->
  K R A F f (initSegment R A a)     ->
  g = extend f a F!f                ->
  b = initSegment R A a :\/: :{a}:  ->
  K R A F g b.
Proof.
Admitted.

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
