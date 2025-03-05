Require Import ZF.Class.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Function.
Require Import ZF.Class.Functional.
Require Import ZF.Class.FunctionalAt.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Range.
Require Import ZF.Class.Relation.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* Binary predicate on classes: F is a function defined on A.                   *)
Definition FunctionOn (F A:Class) : Prop := Function F /\ domain F :~: A.

Proposition FunctionOnImageIsSmall : forall (F A B:Class),
  FunctionOn F A -> Small B -> Small F:[B]:.
Proof.
  intros F A B [H1 _]. apply FunctionImageIsSmall. assumption.
Qed.

(* A function is always a function defined on its domain.                       *)
Proposition FunctionIsFunctionOn : forall (F:Class),
  Function F -> FunctionOn F (domain F).
Proof.
  intros F H1. split. { assumption. } { apply ClassEquivRefl. }
Qed.

(* If F is a function defined on A, then it is a subclass of A x F[A].          *)
Proposition FunctionOnIncl : forall (F A:Class),
  FunctionOn F A -> F :<=: A :x: F:[A]:.
Proof.
  intros F A H1 x H2. destruct H1 as [[H1 H3] H4]. unfold Relation in H1.
  assert (H5 := H1 x H2). destruct H5 as [y [z H5]].
  exists y. exists z. split. 1: assumption. subst. split.
  - apply H4. exists z. assumption.
  - exists y. split. 2: assumption. apply H4. exists z. assumption.
Qed.

(* A function defined on a small class is small.                                *)
Proposition FunctionOnIsSmall : forall (F A:Class),
  FunctionOn F A -> Small A -> Small F.
Proof.

  (* Let F and A be arbitrary classes. *)
  intros F A.

  (* We assume that F is a function defined on A. *)
  intros H1. assert (FunctionOn F A) as A'. { apply H1. } clear A'.

  (* Note in particular that F is a functional class. *)
  assert (H2 := H1). destruct H2 as [[_ H2] _].
  assert (Functional F) as A'. { apply H2. } clear A'.

  (* And we assume that A is small. *)
  intros H3. assert (Small A) as A'. { apply H3. } clear A'.

  (* We need to show that F is small. *)
  assert (Small F) as A'. 2: apply A'.

  (* Being a function defined on A, we have F <= A x F[A]. *)
  apply FunctionOnIncl in H1. assert (F :<=: A :x: F:[A]:) as A'.
    { apply H1. } clear A'.

  (* Thus, in order to prove that F is small ... *)
  apply LesserThanSmallIsSmall with (A :x: F:[A]:). 1: apply H1.

  (* It is sufficient to prove that A x F[A] is small *)
  assert (Small (A :x: F:[A]:)) as A'. 2: apply A'.

  (* To show that this product class is small ... *)
  apply ProdIsSmall.

  (* We need to argue that A is small, which is true by assumption. *)
  - assert (Small A) as A'. 2: apply A'. assumption.

  (* And we need to show that F[A] is small. *)
  - assert (Small F:[A]:) as A'. 2: apply A'.

  (* Which follows from the fact that F is functional and A is small. *)
    apply ImageIsSmall. { apply H2. } { apply H3. }
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

Proposition ComposeIsFunctionOn : forall (F A G B:Class),
  FunctionOn F A ->
  FunctionOn G B ->
  range F :<=: B ->
  FunctionOn (G :.: F) A.
Proof.
  intros F A G B [H1 H2] [H3 H4] H5. split.
  - apply ComposeIsFunction; assumption.
  - apply ClassEquivTran with (domain F). 2: assumption.
    apply ComposeDomainIsSame. apply InclEquivCompatR with B. 2: assumption.
    apply ClassEquivSym. assumption.
Qed.

Proposition FunctionOnEval : forall (F A:Class) (a y:U),
  FunctionOn F A -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A a y [H1 H2] H3. apply FunctionEval. 1: assumption.
  apply H2. assumption.
Qed.

Proposition FunctionOnEvalSatisfies : forall (F A:Class) (a:U),
  FunctionOn F A -> A a -> F :(a,F!a):.
Proof.
  intros F A a [H1 H2] H3. apply FunctionEvalSatisfies. 1: assumption.
  apply H2. assumption.
Qed.

Proposition FunctionOnEvalIsInRange : forall (F A:Class) (a:U),
  FunctionOn F A -> A a -> range F (F!a).
Proof.
  intros F A a [H1 H2] H3. apply FunctionEvalIsInRange. 1: assumption.
  apply H2. assumption.
Qed.

Proposition FunctionOnComposeDomainCharac : forall (F G A B:Class) (a:U),
  FunctionOn F A ->
  FunctionOn G B ->
  domain (G :.: F) a <-> A a /\ B (F!a).
Proof.
  intros F G A B a [H1 H2] [H3 H4]. split; intros H5.
  - apply FunctionComposeDomainCharac in H5. destruct H5 as [H5 H6]. split.
    + apply H2. assumption.
    + apply H4. assumption.
    + assumption.
  - destruct H5 as [H5 H6]. apply FunctionComposeDomainCharac. 1: assumption. split.
    + apply H2. assumption.
    + apply H4. assumption.
Qed.

Proposition FunctionOnComposeEval : forall (F G A B:Class) (a:U),
  FunctionOn F A ->
  FunctionOn G B ->
  A a            ->
  B (F!a)        ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G A B a [H1 H2] [H3 H4] H5 H6.
  apply FunctionComposeEval; try assumption.
  - apply H2. assumption.
  - apply H4. assumption.
Qed.

