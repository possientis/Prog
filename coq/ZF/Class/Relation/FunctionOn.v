Require Import ZF.Class.Core.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.FunctionalAt.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.InvImage.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.OrdPair.

(* F is a function defined on A.                                                *)
Definition FunctionOn (F A:Class) : Prop := Function F /\ domain F :~: A.

(* The direct image of a small class by a function (defined on A) is small.     *)
Proposition ImageIsSmall : forall (F A B:Class),
  FunctionOn F A -> Small B -> Small F:[B]:.
Proof.
  intros F A B H1. apply Function.ImageIsSmall, H1.
Qed.

(* A function is always a function defined on its domain.                       *)
Proposition FunctionIsFunctionOn : forall (F:Class),
  Function F -> FunctionOn F (domain F).
Proof.
  intros F H1. split. { assumption. } { apply EquivRefl. }
Qed.

(* If F is a function defined on A, then it is a subclass of A x F[A].          *)
Proposition InclInProduct : forall (F A:Class),
  FunctionOn F A -> F :<=: A :x: F:[A]:.
Proof.
  intros F A H1 x H2. destruct H1 as [[H1 H3] H4]. unfold Relation in H1.
  assert (H5 := H1 x H2). destruct H5 as [y [z H5]].
  exists y. exists z. split. 1: assumption. subst. split.
  - apply H4. exists z. assumption.
  - exists y. split. 2: assumption. apply H4. exists z. assumption.
Qed.

(* A function defined on a small class is small.                                *)
Proposition IsSmall : forall (F A:Class),
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
  apply InclInProduct in H1. assert (F :<=: A :x: F:[A]:) as A'.
    { apply H1. } clear A'.

  (* Thus, in order to prove that F is small ... *)
  apply InclInSmallIsSmall with (A :x: F:[A]:). 1: apply H1.

  (* It is sufficient to prove that A x F[A] is small *)
  assert (Small (A :x: F:[A]:)) as A'. 2: apply A'.

  (* To show that this product class is small ... *)
  apply Prod.IsSmall.

  (* We need to argue that A is small, which is true by assumption. *)
  - assert (Small A) as A'. 2: apply A'. assumption.

  (* And we need to show that F[A] is small. *)
  - assert (Small F:[A]:) as A'. 2: apply A'.

  (* Which follows from the fact that F is functional and A is small. *)
    apply Image.IsSmall. { apply H2. } { apply H3. }
Qed.

(* Two functions are equal iff they have same domain and coincide pointwise.    *)
Proposition EquivCharac : forall (F A G B:Class),
  FunctionOn F A ->
  FunctionOn G B ->
  F :~: G       <->
  A :~: B /\ forall x, A x -> F!x = G!x.
Proof.
  intros F A G B [H1 H2] [H3 H4].
  assert (F :~: G <->
    domain F :~: domain G /\ forall x, domain F x -> F!x = G!x) as H5.
    { apply Function.EquivCharac; assumption. }
  split; intros H6.
  - apply H5 in H6. destruct H6 as [H6 H7]. clear H5. split.
    + apply EquivTran with (domain F). 1: { apply EquivSym. assumption. }
      apply EquivTran with (domain G); assumption.
    + intros x H8. apply H7, H2. assumption.
  - destruct H6 as [H6 H7]. apply H5. split.
    + apply EquivTran with A. 1: assumption.
      apply EquivTran with B. 1: assumption.
      apply EquivSym. assumption.
    + intros x H8. apply H7, H2. assumption.
Qed.

(* If F defined on A, G defined on B and range F <= B, then G.F defined on A.   *)
Proposition Compose : forall (F A G B:Class),
  FunctionOn F A ->
  FunctionOn G B ->
  range F :<=: B ->
  FunctionOn (G :.: F) A.
Proof.
  intros F A G B [H1 H2] [H3 H4] H5. split.
  - apply Function.Compose; assumption.
  - apply EquivTran with (domain F). 2: assumption.
    apply Compose.DomainIsSame. apply Incl.EquivCompatR with B. 2: assumption.
    apply EquivSym. assumption.
Qed.

(* Characterization of the value at a of a function defined on A when a in A.   *)
Proposition EvalCharac : forall (F A:Class) (a y:U),
  FunctionOn F A -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A a y [H1 H2] H3. apply Function.EvalCharac. 1: assumption.
  apply H2. assumption.
Qed.

(* The ordered pair (a,F!a) satisfies the predicate F when a in A.              *)
Proposition Satisfies : forall (F A:Class) (a:U),
  FunctionOn F A -> A a -> F :(a,F!a):.
Proof.
  intros F A a [H1 H2] H3. apply Function.Satisfies. 1: assumption.
  apply H2. assumption.
Qed.

(* The value at a of a function defined on A lies in the range when a im A.     *)
Proposition IsInRange : forall (F A:Class) (a:U),
  FunctionOn F A -> A a -> range F (F!a).
Proof.
  intros F A a [H1 H2] H3. apply Function.IsInRange. 1: assumption.
  apply H2. assumption.
Qed.

Proposition ImageCharac : forall (F A B: Class), FunctionOn F A ->
  forall y, F:[B]: y <-> exists x, B x /\ A x /\ F!x = y.
Proof.
  intros F A B [H1 H2] y. split; intros H3.
  - apply Function.ImageCharac in H3. 2: assumption.
    destruct H3 as [x [H3 [H4 H5]]]. exists x. split. 1: assumption.
    split. 2: assumption. apply H2. assumption.
  - destruct H3 as [x [H3 [H4 H5]]]. apply Function.ImageCharac. 1: assumption.
    exists x. split. 1: assumption. split. 2: assumption. apply H2. assumption.
Qed.

(* Characterization of the domain of G.F.                                       *)
Proposition DomainOfComposeCharac : forall (F G A B:Class) (a:U),
  FunctionOn F A ->
  FunctionOn G B ->
  domain (G :.: F) a <-> A a /\ B (F!a).
Proof.
  intros F G A B a [H1 H2] [H3 H4]. split; intros H5.
  - apply Function.DomainOfComposeCharac in H5. destruct H5 as [H5 H6]. split.
    + apply H2. assumption.
    + apply H4. assumption.
    + assumption.
  - destruct H5 as [H5 H6].
    apply Function.DomainOfComposeCharac. 1: assumption. split.
    + apply H2. assumption.
    + apply H4. assumption.
Qed.

(* The value at a of G.F is the value at F!a of G when a in A.                  *)
Proposition ComposeEval : forall (F G A B:Class) (a:U),
  FunctionOn F A ->
  FunctionOn G B ->
  A a            ->
  B (F!a)        ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G A B a [H1 H2] [H3 H4] H5 H6.
  apply Function.ComposeEval; try assumption.
  - apply H2. assumption.
  - apply H4. assumption.
Qed.

(* The direct image of the domain is the range.                                 *)
Proposition ImageOfDomainIsRange : forall (F A:Class),
  FunctionOn F A -> F:[A]: :~: range F.
Proof.
  intros F A [H1 H2]. apply EquivTran with F:[domain F]:.
  - apply Image.EquivCompatR, EquivSym. assumption.
  - apply Range.ImageOfDomainIsRange.
Qed.

(* The inverse image of the range is the domain.                                *)
Proposition InvImageOfRangeIsDomain : forall (F A:Class),
  FunctionOn F A -> F^:-1::[range F]: :~: A.
Proof.
  intros F A [H1 H2]. apply EquivTran with (domain F).
  2: assumption. apply InvImageOfRangeIsDomain.
Qed.

(* If F is defined on a small class A, then its range is small.                 *)
Proposition RangeIsSmall : forall (F A:Class),
  FunctionOn F A -> Small A -> Small (range F).
Proof.
  intros F A H1 H2. apply Small.EquivCompat with F:[A]:.
  - apply ImageOfDomainIsRange. assumption.
  - apply ImageIsSmall with A; assumption.
Qed.

(* Characterisation of the range of F.                                          *)
Proposition RangeCharac : forall (F A:Class) (y:U),
  FunctionOn F A -> range F y <-> exists x, A x /\ y = F!x.
Proof.
  intros F A y H1. split; intros [x H2]; exists x.
  - assert (A x) as H3. {
      destruct H1 as [_ H1]. apply H1. exists y. assumption. }
    split. 1: assumption. symmetry. apply (EvalCharac F A); assumption.
  - destruct H2 as [H2 H3]. symmetry in H3.
    apply (EvalCharac F A); assumption.
Qed.

(* If the domain of F is not empty, then neither is the range.                  *)
Proposition RangeIsNotEmpty : forall (F A:Class),
  FunctionOn F A -> A :<>: :0: -> range F :<>: :0:.
Proof.
  intros F A H1 H2. apply HasElem in H2. destruct H2 as [x H2].
  apply HasElem. exists F!x. apply IsInRange with A; assumption.
Qed.

