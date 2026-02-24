Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.InvImage.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.ImageByClass.
Require Import ZF.Set.Union.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Image.

Module CRD := ZF.Class.Relation.Domain.
Module CRF := ZF.Class.Relation.Function.
Module CRL := ZF.Class.Relation.Functional.
Module CRR := ZF.Class.Relation.Relation.

(* An R-transitive set a in class A,                                            *)
Definition Transitive (R A:Class) (a:U) : Prop :=
  forall x y, A x -> R :(x,y): -> y :< a -> x :< a.

Proposition Exists : forall (R A:Class) (a:U),
  WellFounded R A   ->
  toClass a :<=: A  ->
  exists b,
    a :<=: b                                              /\
    toClass b :<=: A                                      /\
    Transitive R A b                                      /\
    (forall x, x :< b -> exists n g,
      Fun g (succ n) b                            /\
      g!:0: :< a                                  /\
      g!n = x                                     /\
      (forall i, i :< n -> R :(g!(succ i),g!i):))         /\
    (forall c,
      a :<=: c          ->
      toClass c :<=: A  ->
      Transitive R A c  ->
      b :<=: c).
Proof.
  intros R A a H1 H2.
  remember (fun y => exists x, A x /\ y = :(x,initSegment R A x):) as B eqn:H3.
  assert (forall x y, B :(x,y): <-> A x /\ y = initSegment R A x) as H4. {
    intros x y. split; intros H4.
    - rewrite H3 in H4. destruct H4 as [u [H4 H5]].
      apply OrdPair.WhenEqual in H5. destruct H5 as [H5 H6]. subst.
      split. 1: assumption. reflexivity.
    - rewrite H3. destruct H4 as [H4 H5]. exists x. split. 1: assumption.
      rewrite H5. reflexivity. }
  assert (CRR.Relation B) as H5. {
    intros y H5. rewrite H3 in H5. destruct H5 as [x [H5 H6]].
    exists x, (initSegment R A x). assumption. }
  assert (CRL.Functional B) as H6. {
    intros x y1 y2 H6 H7.
    apply H4 in H6. destruct H6 as [H6 H8].
    apply H4 in H7. destruct H7 as [H7 H9].
    subst. reflexivity. }
  assert (CRF.Function B) as H7. { split; assumption. }
  assert (CRD.domain B :~: A) as H8. {
    intros x. split; intros H8.
    - destruct H8 as [y H8]. apply H4 in H8. apply H8.
    - exists (initSegment R A x). apply H4. split. 1: assumption. reflexivity. }
  assert (forall x, A x -> B!x = initSegment R A x) as H9. {
    intros x H9. apply EvalOfClass.Charac. 1: assumption.
    - apply H8. assumption.
    - apply H4. split. 1: assumption. reflexivity. }
  remember (fun y => A :/\: R^:-1: :[toClass y]:) as F eqn:H10.
  assert (forall y, toClass y :<=: A -> F y :~: toClass :U(B:[y]:)) as H11. {
    intros y H11 x. split; intros H12.
    - rewrite H10 in H12. destruct H12 as [H12 H13].
      destruct H13 as [z [H13 H14]].
Admitted.
