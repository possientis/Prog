Require Import ZF.Class.Core.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* A class is a function iff it is a relation and it is functional.             *)
Definition Function (F:Class) : Prop := Relation F /\ Functional F.

Proposition ImageIsSmall : forall (F A:Class),
  Function F -> Small A -> Small F:[A]:.
Proof.
  intros F A [_ H1]. apply Image.IsSmall. assumption.
Qed.

(* Two functions are equal iff they have same domain and coincide pointwise.    *)
Proposition EquivCharac : forall (F G:Class),
  Function F ->
  Function G ->
  F :~: G <-> domain F :~: domain G  /\ forall x, domain F x -> F!x = G!x.
Proof.
  intros F G. intros [Hf Gf] [Hg Gg].
  unfold Relation in Hf. unfold Relation in Hg. split; intros H1.
  assert (domain F :~: domain G) as H2. { apply DomainEquivCompat. assumption. }
  - split. 1: assumption. intros x H3.
    assert (domain G x) as H4. { apply H2. assumption. }
    assert (H5 := H3). assert (H6 := H4).
    destruct H3 as [y  H3]. destruct H4 as [y' H4].
    assert (y' = y) as H7. { apply Gf with x.
      - apply H1. assumption.
      - assumption. }
    subst.
    assert (F!x = y) as H8. { apply Eval.Charac; assumption. }
    assert (G!x = y) as H9. { apply Eval.Charac; assumption. }
    subst. symmetry. assumption.
  - destruct H1 as [H1 H2]. intros u. split; intros H3; assert (H4 := H3).
    + apply Hf in H4. destruct H4 as [x [y H4]]. subst.
      assert (domain F x) as H4. { exists y. assumption. }
      assert (F!x = y) as H5. { apply Eval.Charac; assumption. }
      assert (domain G x) as H6. { apply H1. assumption. }
      apply Eval.Charac. { assumption. } { assumption. }
      symmetry. rewrite <- H5. apply H2. assumption.
    + apply Hg in H4. destruct H4 as [x [y H4]]. subst.
      assert (domain G x) as H4. { exists y. assumption. }
      assert (G!x = y) as H5. { apply Eval.Charac; assumption. }
      assert (domain F x) as H6. { apply H1. assumption. }
      apply Eval.Charac. { assumption. } { assumption. }
      rewrite <- H5. apply H2. assumption.
Qed.

(* The composition of two functional classes is a function class.               *)
Proposition FunctionalComposeIsFunction : forall (F G:Class),
  Functional F -> Functional G -> Function (G :.: F).
Proof.
  intros F G Hf Hg. split.
  - apply Compose.IsRelation.
  - apply Compose.IsFunctional; assumption.
Qed.

(* The composition of two function classes is a function class.                 *)
Proposition ComposeIsFunction : forall (F G:Class),
  Function F -> Function G -> Function (G :.: F).
Proof.
  intros F G [_ Hf] [_ Hg]. apply FunctionalComposeIsFunction; assumption.
Qed.

Proposition EvalCharac : forall (F:Class) (a y:U),
  Function F -> domain F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y [_ H1]. apply Eval.Charac. assumption.
Qed.

Proposition EvalSatisfies : forall (F:Class) (a:U),
  Function F -> domain F a -> F :(a,F!a):.
Proof.
  intros F a [_ H1]. apply Eval.Satisfies. assumption.
Qed.

Proposition EvalIsInRange : forall (F:Class) (a:U),
  Function F -> domain F a -> range F (F!a).
Proof.
  intros F a [_ H1]. apply Eval.IsInRange. assumption.
Qed.

Proposition DomainOfComposeCharac : forall (F G:Class) (a:U),
  Function F -> domain (G :.: F) a <-> domain F a /\ domain G F!a.
Proof.
  intros F G a [_ H1]. apply Compose.FunctionalDomainCharac. assumption.
Qed.

Proposition ComposeEval : forall (F G:Class) (a:U),
  Function F     ->
  Function G     ->
  domain F a     ->
  domain G (F!a) ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G a [H1 H2] [H3 H4]. apply Compose.Eval; assumption.
Qed.

