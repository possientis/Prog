Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Image.
Require Import ZF.Class.Range.
Require Import ZF.Class.Relation.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* A class is a function iff it is a relation and it is functional.             *)
Definition Function (F:Class) : Prop := Relation F /\ Functional F.

Proposition FunctionImageIsSmall : forall (F A:Class),
  Function F -> Small A -> Small F:[A]:.
Proof.
  intros F A [_ H1]. apply ImageIsSmall. assumption.
Qed.

(* Two functions are equal iff they have same domain and coincide pointwise.    *)
Proposition FunctionEquivCharac : forall (F G:Class),
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
    assert (F!x = y) as H8. { apply FunctionalEvalCharac; assumption. }
    assert (G!x = y) as H9. { apply FunctionalEvalCharac; assumption. }
    subst. symmetry. assumption.
  - destruct H1 as [H1 H2]. intros u. split; intros H3; assert (H4 := H3).
    + apply Hf in H4. destruct H4 as [x [y H4]]. subst.
      assert (domain F x) as H4. { exists y. assumption. }
      assert (F!x = y) as H5. { apply FunctionalEvalCharac; assumption. }
      assert (domain G x) as H6. { apply H1. assumption. }
      apply FunctionalEvalCharac. { assumption. } { assumption. }
      symmetry. rewrite <- H5. apply H2. assumption.
    + apply Hg in H4. destruct H4 as [x [y H4]]. subst.
      assert (domain G x) as H4. { exists y. assumption. }
      assert (G!x = y) as H5. { apply FunctionalEvalCharac; assumption. }
      assert (domain F x) as H6. { apply H1. assumption. }
      apply FunctionalEvalCharac. { assumption. } { assumption. }
      rewrite <- H5. apply H2. assumption.
Qed.

(* The composition of two functional classes is a function class.               *)
Proposition ComposeIsFunction2 : forall (F G:Class),
  Functional F -> Functional G -> Function (G :.: F).
Proof.
  intros F G Hf Hg. split.
  - apply ComposeIsRelation.
  - apply ComposeIsFunctional; assumption.
Qed.

(* The composition of two function classes is a function class.                 *)
Proposition ComposeIsFunction : forall (F G:Class),
  Function F -> Function G -> Function (G :.: F).
Proof.
  intros F G [_ Hf] [_ Hg]. apply ComposeIsFunction2; assumption.
Qed.

Proposition FunctionEval : forall (F:Class) (a y:U),
  Function F -> domain F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y [_ H1]. apply FunctionalEvalCharac. assumption.
Qed.

Proposition FunctionEvalSatisfies : forall (F:Class) (a:U),
  Function F -> domain F a -> F :(a,F!a):.
Proof.
  intros F a [_ H1]. apply FunctionalEvalSatisfies. assumption.
Qed.

Proposition FunctionEvalIsInRange : forall (F:Class) (a:U),
  Function F -> domain F a -> range F (F!a).
Proof.
  intros F a [_ H1]. apply FunctionalEvalIsInRange. assumption.
Qed.

Proposition FunctionComposeDomainCharac : forall (F G:Class) (a:U),
  Function F -> domain (G :.: F) a <-> domain F a /\ domain G F!a.
Proof.
  intros F G a [_ H1]. apply FunctionalComposeDomainCharac. assumption.
Qed.

Proposition FunctionComposeEval : forall (F G:Class) (a:U),
  Function F     ->
  Function G     ->
  domain F a     ->
  domain G (F!a) ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G a [H1 H2] [H3 H4]. apply FunctionalComposeEval; assumption.
Qed.

