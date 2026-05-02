Require Import ZF.Class.Bounded.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

(* Transporting a 'relation R on A' by F.                                       *)
Definition transport (F R A:Class) : Class := fun x =>
  exists y z, x = :(F!y,F!z): /\ A y /\ A z /\ R :(y,z):.

(* :(F!y,F!z): is in (transport F R A) iff R :(y,z):, given y,z in A.           *)
Proposition Charac2F : forall (F R A B:Class) (y z:U),
  Bij F A B                                   ->
  A y                                         ->
  A z                                         ->
  transport F R A :(F!y,F!z): <-> R :(y,z):.
Proof.
  (* Proof by Claude.                                                           *)
  intros F R A B y z H1 H2 H3. split; intros H4.
  - destruct H4 as [y' [z' [H4 [H5 [H6 H7]]]]].
    apply OrdPair.WhenEqual in H4. destruct H4 as [H4 H8].
    assert (y = y') as H9.  { apply Bij.EvalInjective with F A B; assumption. }
    assert (z = z') as H10. { apply Bij.EvalInjective with F A B; assumption. }
    subst. assumption.
  - exists y, z. split. 1: reflexivity. split. 1: assumption. split; assumption.
Qed.

Proposition IsIncl : forall (F R A:Class),
  Functional F                                ->
  A :<=: domain F                             ->
  transport F R A :<=: F:[A]: :x: F:[A]:.
Proof.
  intros F R A x H1 H2 H3.
  destruct H3 as [y [z [H3 [H4 [H5 _]]]]]. exists F!y, F!z.
  split. 1: assumption. split.
  - exists y. split. 1: assumption. apply EvalOfClass.Satisfies. 1: assumption.
    apply H1. assumption.
  - exists z. split. 1: assumption. apply EvalOfClass.Satisfies. 1: assumption.
    apply H1. assumption.
Qed.

Proposition IsSmall : forall (F R A:Class),
  Functional F                                ->
  A :<=: domain F                             ->
  Small A                                     ->
  Small (transport F R A).
Proof.
  intros F R A H1 H2 H3.
  assert (Small F:[A]:) as H4. { apply Image.IsSmall; assumption. }
  apply Bounded.WhenSmaller with (F:[A]: :x: F:[A]:).
  - apply IsIncl; assumption.
  - apply Prod.IsSmall; assumption.
Qed.

