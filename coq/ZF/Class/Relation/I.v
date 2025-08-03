Require Import ZF.Class.Equiv.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Bijection.
Require Import ZF.Class.Relation.BijectionOn.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.V.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.OrdPair.

(* The class of all ordered pairs of the form (x,x), aka the 'identity' class.  *)
Definition I : Class := fun x => exists y, x = :(y,y):.

Proposition Charac2 : forall (y z:U), I :(y,z): <-> y = z.
Proof.
  intros y z. split; intros H1.
  - destruct H1 as [x H1]. apply WhenEqual in H1.
    destruct H1 as [H1 H2]. subst. reflexivity.
  - subst. exists z. reflexivity.
Qed.

(* I is a functional class.                                                     *)
Proposition IsFunctional : Functional I.
Proof.
  intros x y z H1 H2.
  apply Charac2 in H1. apply Charac2 in H2. subst. reflexivity.
Qed.

(* I is a relation class.                                                       *)
Proposition IsRelation : Relation I.
Proof.
  intros x H1. destruct H1 as [y H1]. exists y. exists y. assumption.
Qed.

(* I is a function class.                                                       *)
Proposition IsFunction : Function I.
Proof.
  split.
    - apply IsRelation.
    - apply IsFunctional.
Qed.

(* The Converse of I is I itself.                                               *)
Proposition Converse : I^:-1: :~: I.
Proof.
  intros x. split; intros H1.
  - destruct H1 as [y [z [H1 H2]]].
    apply Charac2 in H2. subst. apply Charac2. reflexivity.
  - destruct H1 as [y H1]. exists y. exists y.
    split. 1: assumption. apply Charac2. reflexivity.
Qed.

(* I is a one-to-one class.                                                     *)
Proposition IsOneToOne : OneToOne I.
Proof.
  split.
  - apply IsFunctional.
  - apply Functional.EquivCompat with I. 2: apply IsFunctional.
    apply Equiv.Sym, Converse.
Qed.

(* I is a bijection class.                                                      *)
Proposition IsBijection : Bijection I.
Proof.
  split.
  - apply IsRelation.
  - apply IsOneToOne.
Qed.

(* The domain of I is the class of all sets.                                    *)
Proposition Domain : domain I :~: V.
Proof.
  intros x. split; intros H1.
  - apply Logic.I.
  - exists x. apply Charac2. reflexivity.
Qed.

(* The range of I is the class of all sets.                                     *)
Proposition Range : range I :~: V.
Proof.
  intros y. split; intros H1.
  - apply Logic.I.
  - exists y. apply Charac2. reflexivity.
Qed.

(* I is a function class defined on the class of all sets.                      *)
Proposition IsFunctionOn : FunctionOn I V.
Proof.
  split.
  - apply IsFunction.
  - apply Domain.
Qed.

(* I is a bijection class defined on the class of all sets.                     *)
Proposition IsBijectionOn : BijectionOn I V.
Proof.
  split.
  - apply IsBijection.
  - apply Domain.
Qed.

(* I is a bijection class from the class of all sets onto the class of all sets.*)
Proposition IsBij : Bij I V V.
Proof.
  split.
  - apply IsBijectionOn.
  - apply Range.
Qed.

(* The value of I at x is x.                                                    *)
Proposition Eval : forall (x:U), I!x = x.
Proof.
  intros x. apply EvalOfClass.Charac.
  - apply IsFunctional.
  - apply Domain, Logic.I.
  - apply Charac2. reflexivity.
Qed.

(* Given any class R, I is an isomorphism class from V to V w.r. to R (and R).  *)
Proposition IsIsom : forall (R:Class), Isom I R R V V.
Proof.
  intros R. split.
  - apply IsBij.
  - intros x y _ _. split; intros H1.
    + rewrite (Eval x) , (Eval y). assumption.
    + rewrite (Eval x) , (Eval y) in H1. assumption.
Qed.
