Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.Sup.
Require Import ZF.Set.Ordinal.SupOf.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.UnionGen.

Require Import ZF.Notation.Eval.

Module CRD := ZF.Class.Relation.Domain.
Module CFL := ZF.Class.Relation.Functional.

Definition Oracle (F:Class) (a:U) : Class := fun x =>
  exists f y d, x = :(f,y): /\ d = domain f /\
   ((d = :0:      /\ y = a                       )  \/
    (Successor d  /\ y = F! :(sup d, f!(sup d)): )  \/
    (Limit d      /\ y = :\/:_{d} f              )).

Proposition Charac2 : forall (F:Class) (a f y:U),
  Oracle F a :(f,y): <->
  (domain f = :0:       /\ y = a                                         ) \/
  (Successor (domain f) /\ y = F! :(sup (domain f), f!(sup (domain f))): ) \/
  (Limit (domain f)     /\ y = :\/:_{domain f} f                         ).
Proof.
  intros F a f y. split; intros H1.
  - destruct H1 as [f' [y' [d [H1 [H2 H3]]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H4]. subst.
    destruct H3 as [H3|[H3|H3]].
    + left. assumption.
    + right. left. assumption.
    + right. right. assumption.
  - exists f, y, (domain f). split. 1: reflexivity. split. 1: reflexivity.
    destruct H1 as [H1|[H1|H1]].
    + left. assumption.
    + right. left. assumption.
    + right. right. assumption.
Qed.

Proposition IsFunctional : forall (F:Class) (a:U),
  Functional (Oracle F a).
Proof.
  intros F a f y1 y2 H1 H2.
  apply Charac2 in H1. apply Charac2 in H2.
  destruct H1 as [[H1 H3]|[[H1 H3]|[H1 H3]]];
  destruct H2 as [[H2 H4]|[[H2 H4]|[H2 H4]]].
  - subst. reflexivity.
  - exfalso. apply Succ.IsNotZero with (domain f); assumption.
  - exfalso. apply Limit.IsNotZero with (domain f); assumption.
  - exfalso. apply Succ.IsNotZero with (domain f); assumption.
  - subst. reflexivity.
  - exfalso. revert H1. apply Limit.NotSucc. assumption.
  - exfalso. apply Limit.IsNotZero with (domain f); assumption.
  - exfalso. revert H2. apply Limit.NotSucc. assumption.
  - subst. reflexivity.
Qed.

Lemma WhenZero : forall (F G:Class) (a:U), (Oracle F a)!(G :|: :0:) = a.
Proof.
  intros F G a. rewrite RestrictOfClass.WhenEmpty. 2: reflexivity.
  assert (Oracle F a :(:0:,a):) as H1. {
    apply Charac2. left. rewrite Domain.WhenEmpty. 2: reflexivity.
    split; reflexivity. }
  apply EvalOfClass.Charac. 3: assumption.
  - apply IsFunctional.
  - exists a. assumption.
Qed.

Lemma WhenSucc : forall (F G:Class) (a b:U),
  Ordinal b                                     ->
  CFL.Functional G                              ->
  toClass (succ b) :<=: CRD.domain G            ->
  (Oracle F a)!(G:|:(succ b)) = F!:(b,G!b):.
Proof.
  intros F G a b H1 H2 H3.
  remember (G:|:(succ b)) as g eqn:H4.
  assert (domain g = succ b) as H5. {
    rewrite H4. apply RestrictOfClass.DomainWhenIncl; assumption. }
  assert (sup (succ b) = b) as H8. { apply SupOf.WhenSucc. assumption. }
  assert (g!b = G!b) as H10. {
    rewrite H4. apply RestrictOfClass.Eval. 1: assumption. apply Succ.IsIn. }
  assert (Oracle F a :(g,F!:(b,G!b):):) as H11. {
    apply Charac2. right. left. split.
    - rewrite H5. apply Succ.IsSuccessor. assumption.
    - rewrite H5, H8, H10. reflexivity. }
  apply (EvalOfClass.Charac (Oracle F a)). 3: assumption.
  - apply IsFunctional.
  - exists F!:(b,G!b):. assumption.
Qed.

Lemma WhenLimit : forall (F G:Class) (a b:U),
  Limit b                           ->
  CFL.Functional G                  ->
  toClass b :<=: CRD.domain G       ->
  (Oracle F a)!(G:|:b) = :\/:_{b} G.
Proof.
  intros F G a b H1 H2 H3.
  remember (G:|:b) as g eqn:H4.
  assert (domain g = b) as H5. {
    rewrite H4. apply RestrictOfClass.DomainWhenIncl; assumption. }
  assert (b <> :0:) as H7. { apply Limit.Charac. 2: assumption. apply H1. }
  assert (g <> :0:) as H8. {
    intros H8. apply H7. rewrite <- H5. apply SRD.WhenEmpty. assumption. }
  assert (:\/:_{b} g = :\/:_{b} G)as H9. {
    apply UnionGenOfClass.EqualCharac. intros x H9.
    rewrite H4. apply RestrictOfClass.Eval; assumption. }
  assert (Oracle F a :(g,:\/:_{b} G):) as H10. {
    apply Charac2. right. right. split.
    - rewrite H5. assumption.
    - rewrite H5, <- H9. reflexivity. }
  apply EvalOfClass.Charac. 3: assumption.
  - apply IsFunctional.
  - exists :\/:_{b} G. assumption.
Qed.
