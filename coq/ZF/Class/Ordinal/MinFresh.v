Require Import ZF.Class.DiffBySet.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Range.

Module CRF := ZF.Class.Relation.Function.

(* MinFresh A picks the R-minimal element of A not yet in the range of its arg. *)
Definition MinFresh (R A:Class) : Class := fun x =>
  exists f m, x = :(f,m): /\ Minimal R (A :\: range f) m.

Proposition Charac2 : forall (R A:Class) (f m:U),
  MinFresh R A :(f,m): <-> Minimal R (A :\: range f) m.
Proof.
  (* Proof by Claude. *)
  intros R A f m. split; intros H1.
  - destruct H1 as [y [z [H1 H2]]]. apply OrdPair.WhenEqual in H1.
    destruct H1 as [H1 H3]. subst. assumption.
  - exists f. exists m. split. 1: reflexivity. assumption.
Qed.

(* MinFresh R A is functional when R is total on A.                             *)
Proposition IsFunctional : forall (R A:Class),
  Total R A -> Functional (MinFresh R A).
Proof.
  (* Proof by Claude. *)
  intros R A H1 x y1 y2 H2 H3.
  apply Charac2 in H2. apply Charac2 in H3. revert H2 H3.
  apply Minimal.Unique with A. 1: assumption. apply Class.Inter2.IsInclL.
Qed.

(* MinFresh R A is a relation class.                                            *)
Proposition IsRelation : forall (R A:Class), Relation (MinFresh R A).
Proof.
  (* Proof by Claude. *)
  intros R A x H1. destruct H1 as [y [z [H1 _]]].
  exists y. exists z. assumption.
Qed.

(* MinFresh R A is a function class when R is total on A.                       *)
Proposition IsFunction : forall (R A:Class),
  Total R A -> Function (MinFresh R A).
Proof.
  (* Proof by Claude. *)
  intros R A H1. split.
  - apply IsRelation.
  - apply IsFunctional. assumption.
Qed.

(* When F :~: MinFresh R A, F!x is R-minimal in A minus the range of x.         *)
Lemma IsMinimal : forall (R A F:Class) (f:U),
  WellFoundedWellOrd R A                        ->
  F :~: MinFresh R A                            ->
  (A :\: range f) :<>: :0:            ->
  Minimal R (A :\: range f) F!f.
Proof.
  (* Proof by Claude. *)
  intros R A F f H1 H2 H3.
  assert (exists y, Minimal R (A :\: range f) y) as H4. {
    apply WellFoundedWellOrd.HasMinimal with A; try assumption.
    apply Class.Inter2.IsInclL. }
  destruct H4 as [y H4].
  assert (F!f = y) as H5. {
    apply CRF.Eval.
    - apply CRF.EquivCompat with (MinFresh R A).
      + apply Equiv.Sym. assumption.
      + apply IsFunction, H1.
    - apply H2, Charac2. assumption. }
  rewrite H5. assumption.
Qed.
