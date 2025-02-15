Require Import ZF.Class.
Require Import ZF.Class.Bij.
Require Import ZF.Class.Bijection.
Require Import ZF.Class.BijectionOn.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Isom.
Require Import ZF.Class.OneToOne.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Range.
Require Import ZF.Class.Restrict.
Require Import ZF.Class.V.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* The class of all ordered pairs of the form (x,x).                            *)
Definition I : Class := fun x => exists y, x = :(y,y):.

Proposition ICharac2 : forall (y z:U), I :(y,z): <-> y = z.
Proof.
  intros y z. split; intros H1.
  - destruct H1 as [x H1]. apply OrdPairEqual in H1.
    destruct H1 as [H1 H2]. subst. reflexivity.
  - subst. exists z. reflexivity.
Qed.

(* I is a functional class.                                                     *)
Proposition FunctionalI : Functional I.
Proof.
  apply FunctionalSuffice. intros x y z H1 H2.
  apply ICharac2 in H1. apply ICharac2 in H2. subst. reflexivity.
Qed.

(* The domain of I is the class of all sets.                                    *)
Proposition DomainI : domain I :~: V.
Proof.
  intros x. split; intros H1.
  - apply Logic.I.
  - apply DomainCharac. exists x. apply ICharac2. reflexivity.
Qed.

(* The range of I is the class of all sets.                                     *)
Proposition RangeI : range I :~: V.
Proof.
  intros y. split; intros H1.
  - apply Logic.I.
  - apply RangeCharac. exists y. apply ICharac2. reflexivity.
Qed.

(* The value of I at x is x.                                                    *)
Proposition EvalI : forall (x:U), I!x = x.
Proof.
  intros x. apply EvalWhenFunctional.
  - apply FunctionalI.
  - apply DomainI, Logic.I.
  - apply ICharac2. reflexivity.
Qed.
