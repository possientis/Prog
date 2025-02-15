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

(* The domain of I|A is A.                                                      *)
Proposition DomainIA : forall (A:Class), domain (I:|:A) :~: A.
Proof.
  intros A.
  apply ClassEquivTran with (A :/\: domain I). 1: apply DomainOfRestrict.
  apply ClassEquivTran with (A :/\: V).
  - apply InterEquivCompatR, DomainI.
  - apply InterVR.
Qed.

(* The range of I|A is A.                                                       *)
Proposition RangeIA : forall (A:Class), range (I:|:A) :~: A.
Proof.
  intros A y. split; intros H1.
  - apply (proj1 (RangeCharac _ _)) in H1. destruct H1 as [x H1].
    apply RestrictCharac2 in H1. destruct H1 as [H1 H2].
    apply ICharac2 in H2. subst. assumption.
  - apply RangeCharac. exists y. apply RestrictCharac2. split.
    + assumption.
    + apply ICharac2. reflexivity.
Qed.

(* The converse of I|A is I|A itself.                                           *)
Proposition ConverseIA : forall (A:Class),
  (I:|:A)^:-1: :~: (I:|:A).
Proof.
  intros A x. split; intros H1.
  - apply ConverseCharac in H1. destruct H1 as [y [z [H1 H2]]].
    apply RestrictCharac2 in H2. destruct H2 as [H2 [u H3]].
    apply OrdPairEqual in H3. destruct H3 as [H3 H4]. subst.
    apply RestrictCharac2. split. 1: assumption. exists u. reflexivity.
  - apply (proj1 (RestrictCharac _ _ _)) in H1.
    destruct H1 as [y [z [H1 [H2 [u H3]]]]]. apply OrdPairEqual in H3.
    destruct H3 as [H3 H4]. subst. apply ConverseCharac2, RestrictCharac2.
    split. 1: assumption. exists u. reflexivity.
Qed.

(* I|A is a functional class.                                                   *)
Proposition FunctionalIA : forall (A:Class), Functional (I:|:A).
Proof.
  intros A. apply RestrictIsFunctional, FunctionalI.
Qed.

(* If x lies in A, then the value of I|A at x is x.                             *)
Proposition EvalIA : forall (A:Class) (x:U),
  A x -> (I:|:A)!x = x.
Proof.
  intros A x H1. apply eq_trans with I!x.
  - apply EvalRestrict. 2: assumption. apply FunctionalI.
  - apply EvalI.
Qed.

(* I|A is a one-to-one class.                                                   *)
Proposition OneToOneIA : forall (A:Class), OneToOne (I:|:A).
Proof.
  intros A. apply OneToOneIsFunctionalBothWays. split.
  - apply FunctionalIA.
  - apply FunctionalEquivCompat with (I:|:A).
    + apply ClassEquivSym, ConverseIA.
    + apply FunctionalIA.
Qed.

(* I|A is a bijection.                                                          *)
Proposition BijectionIA : forall (A:Class), Bijection (I:|:A).
Proof.
  intros A. split.
  - apply RestrictIsRelation.
  - apply OneToOneIA.
Qed.

(* I|A is a bijection on A.                                                     *)
Proposition BijectionOnIA : forall (A:Class), BijectionOn (I:|:A) A.
Proof.
  intros A. split.
  - apply BijectionIA.
  - apply DomainIA.
Qed.

(* I|A is a bijection from A to A.                                              *)
Proposition BijIA : forall (A:Class), Bij (I:|:A) A A.
Proof.
  intros A. split.
  - apply BijectionOnIA.
  - apply RangeIA.
Qed.

(* I|A is an isomorphism from A to A w.r to R.                                  *)
Proposition IsomIA : forall (R A:Class), Isom (I:|:A) R R A A.
Proof.
  intros R A. split.
  - apply BijIA.
  - intros x y H1 H2.
    assert ((I:|:A)!x = x) as H4. { apply EvalIA. assumption. }
    assert ((I:|:A)!y = y) as H5. { apply EvalIA. assumption. }
    split; intros H3.
    + rewrite H4, H5. assumption.
    + rewrite H4, H5 in H3. assumption.
Qed.
