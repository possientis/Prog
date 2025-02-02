Declare Scope ZF_Set_Eval_scope.
Open    Scope ZF_Set_Eval_scope.

Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Eval.
Require Import ZF.Class.Function.
Require Import ZF.Class.Functional.
Require Import ZF.Class.FunctionalAt.
Require Import ZF.Class.FunctionOn.
Require Import ZF.Class.Image.
Require Import ZF.Class.Rel.
Require Import ZF.Set.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.OrdPair.

(* Evaluate the class F at a, returning a set.                                  *)
Definition eval (F:Class) (a:U) : U := fromClass (Class.Eval.eval F a)
  (EvalIsSmall F a).

Notation "F ! a" := (eval F a)
  (at level 0, no associativity) : ZF_Set_Eval_scope.


(* If F has a value at a, then y corresponds to a iff F!a = y.                  *)
Proposition EvalWhenHasValueAt : forall (F:Class) (a y:U),
  HasValueAt F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y H1. split; intros H2.
  - unfold eval. apply ClassEquivSetEqual.
    apply ClassEquivTran with (Class.Eval.eval F a).
    + apply ToFromClass.
    + apply Class.Eval.EvalWhenHasValueAt; assumption.
  - apply Class.Eval.EvalWhenHasValueAt. 1: assumption.
    unfold eval in H2. rewrite <- H2. apply ClassEquivSym, ToFromClass.
Qed.

(* If F has a value at a, then (a,F!a) satisfies the class F.                   *)
Proposition EvalWhenHasValueAtSatisfies : forall (F:Class) (a:U),
  HasValueAt F a -> F :(a,F!a):.
Proof.
  intros F a H1. apply EvalWhenHasValueAt.
  - assumption.
  - reflexivity.
Qed.

(* If F is functional at a and a lies in domain then F (a,y) iff F!a = y.       *)
Proposition EvalWhenFunctionalAt : forall (F:Class) (a y:U),
  FunctionalAt F a -> domain F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y H1 H2.
  apply EvalWhenHasValueAt, HasValueAtWhenFunctionalAt; assumption.
Qed.

(* If F is functional at a and a lies in domain then (a,F!a) satisfies F.       *)
Proposition EvalWhenFunctionalAtSatisfies : forall (F:Class) (a:U),
  FunctionalAt F a -> domain F a -> F :(a,F!a):.
Proof.
  intros F a H1 H2. apply EvalWhenFunctionalAt.
  - assumption.
  - assumption.
  - reflexivity.
Qed.

(* If F is functional and a lies in domain of F then F (a,y) iff F!a = y.       *)
Proposition EvalWhenFunctional : forall (F:Class) (a y:U),
  Functional F -> domain F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y H1 H2.
  apply EvalWhenHasValueAt, HasValueAtWhenFunctional; assumption.
Qed.

(* If F is functional and a lies in domain of F then (a,F!a) satisfies F.       *)
Proposition EvalWhenFunctionalSatisfies : forall (F:Class) (a:U),
  Functional F -> domain F a -> F :(a,F!a):.
Proof.
  intros F a H1 H2. apply EvalWhenFunctionalAtSatisfies. 2: assumption.
  apply FunctionalIsFunctionalAt. assumption.
Qed.

(* If F has no value at a then F!a is the empty set.                            *)
Proposition EvalWhenNotHasValueAt : forall (F:Class) (a:U),
  ~ HasValueAt F a -> F!a = :0:.
Proof.
  intros F a H1. apply ClassEquivSetEqual. unfold eval, zero, SetZero, empty.
  apply ClassEquivTran with (Class.Eval.eval F a). 1: apply ToFromClass.
  apply ClassEquivTran with :0:.
  - apply Class.Eval.EvalWhenNotHasValueAt. assumption.
  - apply ClassEquivSym, ToFromClass.
Qed.

(* If F is not functional at a then F!a is the empty set.                       *)
Proposition EvalWhenNotFunctionalAt : forall (F:Class) (a:U),
  ~ FunctionalAt F a -> F!a = :0:.
Proof.
  intros F a H1. apply EvalWhenNotHasValueAt. intros H2. apply H1.
  apply HasValueAtAsInter. assumption.
Qed.

(* If a is not in domain of F then F!a is the empty set.                        *)
Proposition EvalWhenNotInDomain : forall (F:Class) (a:U),
  ~ domain F a -> F!a = :0:.
Proof.
  intros F a H1. apply EvalWhenNotHasValueAt. intros H2. apply H1.
  apply HasValueAtAsInter. assumption.
Qed.

(* Characterisation of the domain of G.F in terms of the eval F!a.              *)
Proposition ComposeDomainEvalCharac : forall (F G:Class) (a:U),
  FunctionalAt F a -> domain (G :.: F) a <-> domain F a /\ domain G F!a.
Proof.
  intros F G a H1. split; intros H2.
  - split.
    + apply ComposeDomainIsSmaller with G. assumption.
    + apply (proj1 (DomainCharac _ _)) in H2. destruct H2 as [z H2].
      apply ComposeCharac2 in H2. destruct H2 as [y [H2 H3]].
      apply DomainCharac. exists z.
      assert (F!a = y) as H4. {
        apply EvalWhenFunctionalAt. 1: assumption. 2: assumption.
        apply DomainCharac. exists y. assumption.
      }
      rewrite H4. assumption.
  - destruct H2 as [H2 H3]. assert (H4 := H2).
    apply (proj1 (DomainCharac _ _)) in H2. destruct H2 as [y H2].
    apply (proj1 (DomainCharac _ _)) in H3. destruct H3 as [z H3].
    apply DomainCharac. exists z. apply ComposeCharac2. exists y.
    split. 1: assumption.
    assert (F!a = y) as H5. { apply EvalWhenFunctionalAt; assumption. }
    rewrite <- H5. assumption.
Qed.

(* G.F is functional at a if F is, G is functional at F!a and a lies in domain. *)
Proposition ComposeIsFunctionalAt : forall (F G:Class) (a:U),
  FunctionalAt F a          ->
  FunctionalAt G (F!a)      ->
  domain F a                ->
  FunctionalAt (G :.: F) a.
Proof.
  intros F G a H1 H2 H3. apply FunctionalAtCharac2. intros z1 z2 H4 H5.
  apply ComposeCharac2 in H4. destruct H4 as [y1 [H4 H6]].
  apply ComposeCharac2 in H5. destruct H5 as [y2 [H5 H7]].
  assert (F!a = y1) as H8. { apply EvalWhenFunctionalAt; assumption. }
  assert (F!a = y2) as H9. { apply EvalWhenFunctionalAt; assumption. }
  subst. apply FunctionalAtCharac1 with G (F!a); assumption.
Qed.

(* Evaluating the composed class G.F at a, from evaluations of F and G.         *)
Proposition EvalComposeAt : forall (F G:Class) (a:U),
  FunctionalAt F a        ->
  FunctionalAt G (F!a)    ->
  domain (G :.: F) a      ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G a H1 H2 H3. assert (H4 := H3).
  apply ComposeDomainEvalCharac in H4. 2: assumption.
  destruct H4 as [H4 H5]. assert (H6 := H4). assert (H7 := H5).
  apply (proj1 (DomainCharac _ _)) in H4. destruct H4 as [y H4].
  apply (proj1 (DomainCharac _ _)) in H5. destruct H5 as [z H5].
  assert (F!a = y) as H8.     { apply EvalWhenFunctionalAt; assumption. }
  assert (G!(F!a) = z) as H9. { apply EvalWhenFunctionalAt; assumption. }
  assert (FunctionalAt (G :.: F) a) as H10. { apply ComposeIsFunctionalAt; assumption. }
  assert ((G :.: F) :(a,z):) as H11. {
    apply ComposeCharac2. exists y. split. 1: assumption. rewrite <- H8. assumption.
  }
  apply EvalWhenFunctionalAt.
  - assumption.
  - assumption.
  - rewrite H9. assumption.
Qed.

(* Evaluating the composed class G.F at a, from evaluations of F and G.         *)
Proposition EvalCompose : forall (F G:Class) (a:U),
  Functional F -> Functional G -> domain (G :.: F) a -> (G :.: F)!a = G!(F!a).
Proof.
  intros F G a H1 H2 H3. apply EvalComposeAt.
  - apply FunctionalIsFunctionalAt. assumption.
  - apply FunctionalIsFunctionalAt. assumption.
  - assumption.
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
    assert (H5 := H3). assert (H6 := H4).
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
  - destruct H1 as [H1 H2]. intros u. split; intros H3; assert (H4 := H3).
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

(* Two functions are equal iff they have same domain and coincide pointwise.    *)
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

(* Characterisation of the direct image F[A] in terms of evaluations of F.      *)
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


(* Characterisation of the inverse image F^(-1)[A] in terms of evaluations of F.*)
Proposition InvImageEvalCharac : forall (F B:Class), Functional F ->
  forall x, F^:-1: :[B]: x <-> domain F x /\ B F!x.
Proof.
  intros F B H1 x. split; intros H2.
  - apply (proj1 (ImageCharac _ _ _)) in H2. destruct H2 as [y [H2 H3]].
    apply (proj1 (ConverseCharac2 _ _ _)) in H3.
    assert (domain F x) as H4. { apply DomainCharac. exists y. assumption. }
    split. 1: assumption.
    assert (F!x = y) as H5. { apply EvalWhenFunctional; assumption. }
    rewrite H5. assumption.
  - destruct H2 as [H2 H3]. apply ImageCharac. exists (F!x). split. 1: assumption.
    apply ConverseCharac2. apply EvalWhenFunctionalSatisfies; assumption.
Qed.


