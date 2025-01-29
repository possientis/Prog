Require Import ZF.Class.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Function.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Range.
Require Import ZF.Class.Rel.
Require Import ZF.Class.Small.

(* Binary predicate on classes: F is a function defined on A.                   *)
Definition FunctionOn (F A:Class) : Prop := Function F /\ domain F :~: A.

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
  intros F A H1 x H2. destruct H1 as [[H1 H3] H4]. unfold Rel in H1.
  remember (H1 x H2) as H5 eqn:E. clear E. destruct H5 as [y [z H5]].
  apply ProdCharac. exists y. exists z. split. 1: assumption. subst. split.
  - apply H4. apply DomainCharac. exists z. assumption.
  - apply ImageCharac. exists y. split.
    + apply H4, DomainCharac. exists z. assumption.
    + assumption.
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
  remember H1 as H2 eqn:E. clear E. destruct H2 as [[_ H2] _].
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
