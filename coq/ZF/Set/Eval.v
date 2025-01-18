Declare Scope ZF_Set_Eval_scope.
Open    Scope ZF_Set_Eval_scope.

Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Eval.
Require Import ZF.Class.Function.
Require Import ZF.Class.Functional.
Require Import ZF.Class.FunctionOn.
Require Import ZF.Class.Image.
Require Import ZF.Class.Rel.
Require Import ZF.Core.Dot.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Image.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.OrdPair.

Definition eval (F:Class) (a:U) : U := fromClass (Class.Eval.eval F a)
  (EvalIsSmall F a).

Notation "F ! a" := (eval F a)
  (at level 0, no associativity) : ZF_Set_Eval_scope.

Proposition EvalWhenFunctional : forall (F:Class) (a y:U),
  Functional F -> domain F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y H1 H2. split; intros H3.
  - apply SameClassEqual. unfold eval.
    apply ClassEquivTran with (Class.Eval.eval F a).
    + apply ToFromClass.
    + apply Class.Eval.EvalWhenFunctional; assumption.
  - apply Class.Eval.EvalWhenFunctional.
    + assumption.
    + assumption.
    + rewrite <- H3. unfold eval. apply ClassEquivSym, ToFromClass.
Qed.

Proposition EvalCompose : forall (F G:Class) (a:U),
  Functional F -> Functional G -> domain (G :.: F) a -> (G :.: F)!a = G!(F!a).
Proof.
  intros F G a' H1 H2 H3. remember H3 as H3' eqn:E. clear E.
  apply (proj1 (DomainCharac _ _)) in H3'.
  destruct H3' as [z' H3']. remember H3' as H12 eqn:E. clear E.
  apply ComposeCharac in H3'.
  destruct H3' as [a [y [z [H3' [H4 H5]]]]]. apply OrdPairEqual in H3'.
  destruct H3' as [H3' H6]. subst.
  assert (Functional (G :.: F)) as H7. { apply ComposeIsFunctional; assumption. }
  assert (domain F a) as H8. { apply DomainCharac. exists y. assumption. }
  assert (domain G y) as H9. { apply DomainCharac. exists z. assumption. }
  assert (F!a = y) as H10. { apply EvalWhenFunctional; assumption. } rewrite H10.
  assert (G!y = z) as H11. { apply EvalWhenFunctional; assumption. } rewrite H11.
  apply EvalWhenFunctional; assumption.
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

Proposition FunctionOnEquivCharac : forall (F A G B:Class),
  FunctionOn F A ->
  FunctionOn G B ->
  F :~: G       <->
  A :~: B /\ forall x, A x -> F!x = G!x.
Proof.
  intros F A G B [H1 H2] [H3 H4].
  assert (F :~: G <->
    domain F :~: domain G /\ forall x, domain F x -> F!x = G!x) as H5.
    { apply FunctionEquivCharac; assumption. }
  split; intros H6.
  - apply H5 in H6. destruct H6 as [H6 H7]. clear H5. split.
    + apply ClassEquivTran with (domain F). 1: { apply ClassEquivSym. assumption. }
      apply ClassEquivTran with (domain G); assumption.
    + intros x H8. apply H7, H2. assumption.
  - destruct H6 as [H6 H7]. apply H5. split.
    + apply ClassEquivTran with A. 1: assumption.
      apply ClassEquivTran with B. 1: assumption.
      apply ClassEquivSym. assumption.
    + intros x H8. apply H7, H2. assumption.
Qed.

Proposition ImageEvalCharac : forall (F A: Class), Functional F ->
  forall y, F:[A]: y <-> exists x, A x /\ domain F x /\ F!x = y.
Proof.
  intros F A H1 y. split; intros H2.
  - apply (proj1 (ImageCharac _ _ _)) in H2. destruct H2 as [x [H2 H3]].
    exists x. split. 1: assumption.
    assert (domain F x) as H4. { apply DomainCharac. exists y. assumption. } split.
    + assumption.
    + apply EvalWhenFunctional; assumption.
  - destruct H2 as [x [H2 [H3 H4]]].
    apply ImageCharac. exists x. split. 1: assumption.
    apply EvalWhenFunctional; assumption.
Qed.

