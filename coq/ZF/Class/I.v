Require Import ZF.Class.
Require Import ZF.Class.Bij.
Require Import ZF.Class.Bijection.
Require Import ZF.Class.BijectionOn.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Function.
Require Import ZF.Class.Functional.
Require Import ZF.Class.FunctionOn.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Isom.
Require Import ZF.Class.OneToOne.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Range.
Require Import ZF.Class.Relation.
Require Import ZF.Class.Restrict.
Require Import ZF.Class.V.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* The class of all ordered pairs of the form (x,x), aka the 'identity' class.  *)
Definition I : Class := fun x => exists y, x = :(y,y):.

Proposition ICharac2 : forall (y z:U), I :(y,z): <-> y = z.
Proof.
  intros y z. split; intros H1.
  - destruct H1 as [x H1]. apply OrdPairEqual in H1.
    destruct H1 as [H1 H2]. subst. reflexivity.
  - subst. exists z. reflexivity.
Qed.

(* I is a functional class.                                                     *)
Proposition IIsFunctional : Functional I.
Proof.
  apply FunctionalSuffice. intros x y z H1 H2.
  apply ICharac2 in H1. apply ICharac2 in H2. subst. reflexivity.
Qed.

(* I is a relation class.                                                       *)
Proposition IIsRelation : Relation I.
Proof.
  intros x H1. destruct H1 as [y H1]. exists y. exists y. assumption.
Qed.

(* I is a function class.                                                       *)
Proposition IIsFunction : Function I.
Proof.
  split.
    - apply IIsRelation.
    - apply IIsFunctional.
Qed.

(* The Converse of I is I itself.                                               *)
Proposition IConverse : I^:-1: :~: I.
Proof.
  intros x. split; intros H1.
  - apply ConverseCharac in H1. destruct H1 as [y [z [H1 H2]]].
    apply ICharac2 in H2. subst. apply ICharac2. reflexivity.
  - destruct H1 as [y H1]. apply ConverseCharac. exists y. exists y.
    split. 1: assumption. apply ICharac2. reflexivity.
Qed.

(* I is a one-to-one class.                                                     *)
Proposition IIsOneToOne : OneToOne I.
Proof.
  apply OneToOneCharac. split.
  - apply IIsFunctional.
  - apply FunctionalEquivCompat with I. 2: apply IIsFunctional.
    apply ClassEquivSym, IConverse.
Qed.

(* I is a bijection class.                                                      *)
Proposition IIsBijection : Bijection I.
Proof.
  split.
  - apply IIsRelation.
  - apply IIsOneToOne.
Qed.

(* The domain of I is the class of all sets.                                    *)
Proposition IDomain : domain I :~: V.
Proof.
  intros x. split; intros H1.
  - apply Logic.I.
  - apply DomainCharac. exists x. apply ICharac2. reflexivity.
Qed.

(* The range of I is the class of all sets.                                     *)
Proposition IRange : range I :~: V.
Proof.
  intros y. split; intros H1.
  - apply Logic.I.
  - apply RangeCharac. exists y. apply ICharac2. reflexivity.
Qed.

(* I is a function class defined on the class of all sets.                      *)
Proposition IIsFunctionOn : FunctionOn I V.
Proof.
  split.
  - apply IIsFunction.
  - apply IDomain.
Qed.

(* I is a bijection class defined on the class of all sets.                     *)
Proposition IIsBijectionOn : BijectionOn I V.
Proof.
  split.
  - apply IIsBijection.
  - apply IDomain.
Qed.

(* I is a bijection class from the class of all sets onto the class of all sets.*)
Proposition IIsBij : Bij I V V.
Proof.
  split.
  - apply IIsBijectionOn.
  - apply IRange.
Qed.

(* The value of I at x is x.                                                    *)
Proposition IEval : forall (x:U), I!x = x.
Proof.
  intros x. apply FunctionalEval.
  - apply IIsFunctional.
  - apply IDomain, Logic.I.
  - apply ICharac2. reflexivity.
Qed.

(* Given any class R, I is an isomorphism class from V to V w.r. to R (and R).  *)
Proposition IIsIsom : forall (R:Class), Isom I R R V V.
Proof.
  intros R. split.
  - apply IIsBij.
  - intros x y _ _. split; intros H1.
    + rewrite (IEval x) , (IEval y). assumption.
    + rewrite (IEval x) , (IEval y) in H1. assumption.
Qed.
