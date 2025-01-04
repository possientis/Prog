Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Rel.
Require Import ZF.Core.Dot.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* A class is a function iff it is a relation and it is functional.             *)
Definition Function (F:Class) : Prop := Rel F /\ Functional F.

Proposition ComposeIsFunction : forall (F G:Class),
  Functional F -> Functional G -> Function (G :.: F).
Proof.
  intros F G Hf Hg. split.
  - apply ComposeIsRelation.
  - apply ComposeIsFunctional; assumption.
Qed.

(* Weaker result but convenient                                                 *)
Proposition ComposeIsFunction2 : forall (F G:Class),
  Function F -> Function G -> Function (G :.: F).
Proof.
  intros F G [_ Hf] [_ Hg]. apply ComposeIsFunction; assumption.
Qed.

(* Two functions are equal iff they have same domain and coincide pointwise.    *)
Proposition FunctionEquivCharac : forall (F G:Class),
  Function F ->
  Function G ->
  F :~: G <-> domain F :~: domain G  /\ forall x, domain F x -> F!x = G!x.
Proof.
  intros F G. intros [Hf Gf] [Hg Gg].
  unfold Rel in Hf. unfold Rel in Hg. split; intros H1.
  assert (domain F :~: domain G) as H2. { apply DomainEquivCompat. assumption. }
  - split. 1: assumption. intros x H3.
    assert (domain G x) as H4. { apply H2. assumption. }
    remember H3 as H5 eqn:E. clear E. remember H4 as H6 eqn:E. clear E.
    apply (proj1 (DomainCharac _ _)) in H3. destruct H3 as [y  H3].
    apply (proj1 (DomainCharac _ _)) in H4. destruct H4 as [y' H4].
    assert (y' = y) as H7. {
      apply FunctionalCharac1 with F x.
      - assumption.
      - apply H1. assumption.
      - assumption.
    } subst.
    assert (F!x = y) as H8. { apply EvalWhenFunctional; assumption. }
    assert (G!x = y) as H9. { apply EvalWhenFunctional; assumption. }
    subst. symmetry. assumption.
  - destruct H1 as [H1 H2]. intros u. split; intros H3;
    remember H3 as H4 eqn:E;clear E.
    + apply Hf in H4. destruct H4 as [x [y H4]]. subst.
      assert (domain F x) as H4. { apply DomainCharac. exists y. assumption. }
      assert (F!x = y) as H5. { apply EvalWhenFunctional; assumption. }
      assert (domain G x) as H6. { apply H1. assumption. }
      apply EvalWhenFunctional. { assumption. } { assumption. }
      symmetry. rewrite <- H5. apply H2. assumption.
    + apply Hg in H4. destruct H4 as [x [y H4]]. subst.
      assert (domain G x) as H4. { apply DomainCharac. exists y. assumption. }
      assert (G!x = y) as H5. { apply EvalWhenFunctional; assumption. }
      assert (domain F x) as H6. { apply H1. assumption. }
      apply EvalWhenFunctional. { assumption. } { assumption. }
      rewrite <- H5. apply H2. assumption.
Qed.
