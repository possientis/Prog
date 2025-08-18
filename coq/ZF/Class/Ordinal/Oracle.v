Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.NonLimit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.Sup.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.UnionGen.

Module CRD := ZF.Class.Relation.Domain.
Module CFL := ZF.Class.Relation.Functional.

Module SRD := ZF.Set.Relation.Domain.
Module SFL := ZF.Set.Relation.Functional.

Definition Oracle (F:Class) (a:U) : Class := fun x => exists f y, x = :(f,y): /\
  ((f =  :0:                        /\ y = a                     )  \/
   (f <> :0: /\ NonLimit (domain f) /\ y = F!(f!(sup (domain f))))  \/
   (f <> :0: /\ Limit    (domain f) /\ y = :\/:_{domain f} f     )   ).

Proposition Charac2 : forall (F:Class) (a f y:U),
  Oracle F a :(f,y): <->
  ((f =  :0:                        /\ y = a                     ) \/
   (f <> :0: /\ NonLimit (domain f) /\ y = F!(f!(sup (domain f)))) \/
   (f <> :0: /\ Limit    (domain f) /\ y = :\/:_{domain f} f     )  ).
Proof.
  intros F a f y. unfold Oracle. split; intros H1.
  - destruct H1 as [g [z [H1 H2]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3]. subst. assumption.
  - exists f. exists y. split. 1: reflexivity. assumption.
Qed.

Proposition IsFunctional : forall (F:Class) (a:U),
  CFL.Functional (Oracle F a).
Proof.
  intros F a f y z H1 H2. apply Charac2 in H1. apply Charac2 in H2.
  destruct H1 as [[H1 H3]|[[H1 H3]|[H1 H3]]];
  destruct H2 as [[H2 H4]|[[H2 H4]|[H2 H4]]].
  - subst. reflexivity.
  - exfalso. apply H2. assumption.
  - exfalso. apply H2. assumption.
  - exfalso. apply H1. assumption.
  - destruct H3 as [_ H3]. destruct H4 as [_ H4]. subst. reflexivity.
  - destruct H3 as [H3 _]. destruct H4 as [H4 _].
    exfalso. apply Limit.NotBoth with (domain f); assumption.
  - exfalso. apply H1. assumption.
  - destruct H3 as [H3 _]. destruct H4 as [H4 _].
    exfalso. apply Limit.NotBoth with (domain f); assumption.
  - destruct H3 as [_ H3]. destruct H4 as [_ H4]. subst. reflexivity.
Qed.

Lemma L1 : forall (F G:Class) (a:U), (Oracle F a)!(G :|: :0:) = a.
Proof.
  intros F G a. rewrite RestrictOfClass.WhenEmpty. 2: reflexivity.
  assert (Oracle F a :(:0:,a):) as H1. { apply Charac2. left. split; reflexivity. }
  apply EvalOfClass.Charac. 3: assumption.
  - apply IsFunctional.
  - exists a. assumption.
Qed.

Lemma L2 : forall (F G:Class) (a b:U),
  Ordinal b                               ->
  CFL.Functional G                        ->
  toClass (succ b) :<=: CRD.domain G      ->
  (Oracle F a)!(G:|:(succ b)) = F!(G!b).
Proof.
  intros F G a b H1 H2 H3.
  remember (G:|:(succ b)) as g eqn:H4.
  assert (domain g = succ b) as H5. {
    rewrite H4. apply RestrictOfClass.DomainWhenIncl; assumption. }
  assert (NonLimit (succ b)) as H6. { apply NonLimit.HasSucc. assumption. }
  assert (succ b <> :0:) as H7. { apply Succ.IsNotEmpty. }
  assert (sup (succ b) = b) as H8. { apply Sup.WhenSucc. assumption. }
  assert (g <> :0:) as H9. {
    intros H9. apply H7. rewrite <- H5. apply SRD.WhenEmpty. assumption. }
  assert (g!b = G!b) as H10. {
    rewrite H4. apply RestrictOfClass.Eval. 1: assumption. apply Succ.IsIn. }
  assert (Oracle F a :(g,F!(G!b)):) as H11. {
    apply Charac2. right. left. split. 1: assumption. split.
    - rewrite H5. assumption.
    - rewrite H5, H8, H10. reflexivity. }
  apply EvalOfClass.Charac. 3: assumption.
  - apply IsFunctional.
  - exists F!(G!b). assumption.
Qed.
