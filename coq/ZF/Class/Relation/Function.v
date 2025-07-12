Require Import ZF.Class.Equiv.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.InvImage.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.


(* A class is a function iff it is a relation and it is functional.             *)
Definition Function (F:Class) : Prop := Relation F /\ Functional F.

(* Two functions are equal iff they have same domain and coincide pointwise.    *)
Proposition EquivCharac : forall (F G:Class),
  Function F ->
  Function G ->
  F :~: G   <->
  domain F :~: domain G  /\ forall x, domain F x -> F!x = G!x.
Proof.
  intros F G. intros [Hf Gf] [Hg Gg].
  split; intros H1.
  assert (domain F :~: domain G) as H2. { apply Domain.EquivCompat. assumption. }
  - split. 1: assumption. intros x H3.
    assert (domain G x) as H4. { apply H2. assumption. }
    assert (H5 := H3). assert (H6 := H4).
    destruct H3 as [y  H3]. destruct H4 as [y' H4].
    assert (y' = y) as H7. { apply Gf with x.
      - apply H1. assumption.
      - assumption. }
    subst.
    assert (F!x = y) as H8. { apply EvalOfClass.Charac; assumption. }
    assert (G!x = y) as H9. { apply EvalOfClass.Charac; assumption. }
    subst. symmetry. assumption.
  - destruct H1 as [H1 H2]. intros u. split; intros H3; assert (H4 := H3).
    + apply Hf in H4. destruct H4 as [x [y H4]]. subst.
      assert (domain F x) as H4. { exists y. assumption. }
      assert (F!x = y) as H5. { apply EvalOfClass.Charac; assumption. }
      assert (domain G x) as H6. { apply H1. assumption. }
      apply EvalOfClass.Charac. { assumption. } { assumption. }
      symmetry. rewrite <- H5. apply H2. assumption.
    + apply Hg in H4. destruct H4 as [x [y H4]]. subst.
      assert (domain G x) as H4. { exists y. assumption. }
      assert (G!x = y) as H5. { apply EvalOfClass.Charac; assumption. }
      assert (domain F x) as H6. { apply H1. assumption. }
      apply EvalOfClass.Charac. { assumption. } { assumption. }
      rewrite <- H5. apply H2. assumption.
Qed.

(* The direct image of the domain is the range. F need not be a function.       *)
Proposition ImageOfDomain : forall (F:Class),
  F:[domain F]: :~: range F.
Proof.
  apply Range.ImageOfDomain.
Qed.

(* A function is a subclass of the product of its domain and image thereof.     *)
Proposition IsIncl : forall (F:Class),
  Function F -> F :<=: (domain F) :x: F:[domain F]:.
Proof.
  intros F H1. apply Relation.IsIncl, H1.
Qed.

(* The direct image by a function of a small class is small.                    *)
Proposition ImageIsSmall : forall (F A:Class),
  Function F -> Small A -> Small F:[A]:.
Proof.
  intros F A [_ H1]. apply Image.IsSmall. assumption.
Qed.

(* A function class with a small domain is small.                               *)
Proposition IsSmall : forall (F:Class),
  Function F -> Small (domain F) -> Small F.
Proof.
  intros F H1. apply Relation.IsSmall; apply H1.
Qed.

(* The inverse image of the range is the domain. F need not be a function.      *)
Proposition InvImageOfRange : forall (F:Class),
  F^:-1::[range F]: :~: domain F.
Proof.
  apply InvImage.OfRange.
Qed.

(* If a function has a small domain then its range is small.                    *)
Proposition RangeIsSmall : forall (F:Class),
  Function F -> Small (domain F) -> Small (range F).
Proof.
  intros F H1 H2. apply Small.EquivCompat with F:[domain F]:.
  - apply ImageOfDomain.
  - apply ImageIsSmall; assumption.
Qed.

(* The composition of two functional classes is a function class.               *)
Proposition FunctionalCompose : forall (F G:Class),
  Functional F -> Functional G -> Function (G :.: F).
Proof.
  intros F G Hf Hg. split.
  - apply Compose.IsRelation.
  - apply Compose.IsFunctional; assumption.
Qed.

(* The composition of two function classes is a function class.                 *)
Proposition Compose : forall (F G:Class),
  Function F -> Function G -> Function (G :.: F).
Proof.
  intros F G [_ Hf] [_ Hg]. apply FunctionalCompose; assumption.
Qed.

Proposition EvalCharac : forall (F:Class) (a y:U),
  Function F -> domain F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y [_ H1]. apply EvalOfClass.Charac. assumption.
Qed.

Proposition Satisfies : forall (F:Class) (a:U),
  Function F -> domain F a -> F :(a,F!a):.
Proof.
  intros F a [_ H1]. apply EvalOfClass.Satisfies. assumption.
Qed.

Proposition IsInRange : forall (F:Class) (a:U),
  Function F -> domain F a -> range F (F!a).
Proof.
  intros F a [_ H1]. apply EvalOfClass.IsInRange. assumption.
Qed.

Proposition ImageCharac : forall (F A: Class), Function F ->
  forall y, F:[A]: y <-> exists x, A x /\ domain F x /\ F!x = y.
Proof.
  intros F A [_ H1]. apply EvalOfClass.ImageCharac. assumption.
Qed.

Proposition ImageSetCharac : forall (F:Class) (a:U), Function F ->
  forall y, y :< F:[a]: <-> exists x, x :< a /\ domain F x /\ F!x = y.
Proof.
  intros F a H1. intros y. split; intros H2.
  - apply ImageByClass.Charac in H2. 2: apply H1. destruct H2 as [x [H2 H3]].
    assert (domain F x) as H4. { exists y. assumption. }
    exists x. split. 1: assumption. split. 1: assumption.
    apply EvalCharac; assumption.
  - destruct H2 as [x [H2 [H3 H4]]]. apply ImageByClass.CharacRev with x.
    + apply H1.
    + assumption.
    + apply EvalCharac; assumption.
Qed.

Proposition DomainOfCompose : forall (F G:Class) (a:U),
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

Proposition RangeCharac : forall (F:Class) (y:U),
  Function F -> range F y <-> exists x, domain F x /\ y = F!x.
Proof.
  intros F y H1. split; intros H2.
  - destruct H2 as [x H2]. exists x. split.
    + exists y. assumption.
    + symmetry. apply EvalCharac; try assumption. exists y. assumption.
  - destruct H2 as [x [H2 H3]]. exists x. apply EvalCharac; try assumption.
    symmetry. assumption.
Qed.

(* If the domain of F is not empty, then neither is the range.                  *)
Proposition RangeIsNotEmpty : forall (F:Class),
  domain F :<>: :0: -> range F :<>: :0:.
Proof.
  apply Range.IsNotEmpty.
Qed.

Proposition IsRestrict : forall (F:Class),
  Function F -> F :~: F :|: domain F.
Proof.
  intros F H1. apply Restrict.RelationIsRestrict, H1.
Qed.

