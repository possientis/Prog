Require Import ZF.Class.Core.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Bijection.
Require Import ZF.Class.Relation.BijectionOn.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.I.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.V.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

(* I|A is the restriction of the identity class I to the class A.               *)
Proposition IACharac : forall (A:Class) (x:U),
  (I:|:A) x <-> exists y, A y /\ x = :(y,y):.
Proof.
  intros A x. split; intros H1.
  - destruct H1 as [y [z [H1 [H2 H3]]]]. apply ICharac2 in H3. subst.
    exists z. split. 1: assumption. reflexivity.
  - destruct H1 as [y [H1 H2]]. exists y. exists y.
    split. 1: assumption. split. 1: assumption. apply ICharac2. reflexivity.
Qed.

Proposition IACharac2 : forall (A:Class) (y z:U),
  (I:|:A) :(y,z): <-> A y /\ y = z.
Proof.
  intros A y z. split; intros H1.
  - apply Restrict.Charac2 in H1. destruct H1 as [H1 H2].
    apply ICharac2 in H2. subst. split. 1: assumption. reflexivity.
  - destruct H1 as [H1 H2]. subst. apply Restrict.Charac2.
    split. 1: assumption. apply ICharac2. reflexivity.
Qed.

(* I|A is a functional class.                                                   *)
Proposition IAIsFunctional : forall (A:Class), Functional (I:|:A).
Proof.
  intros A. apply Restrict.IsFunctional, IIsFunctional.
Qed.

(* I|A is a relation class.                                                     *)
Proposition IAIsRelation : forall (A:Class), Relation (I:|:A).
Proof.
  intros A. apply Restrict.IsRelation.
Qed.

(* I|A is a function class.                                                     *)
Proposition IAIsFunction : forall (A:Class), Function (I:|:A).
Proof.
  intros A. split.
  - apply IAIsRelation.
  - apply IAIsFunctional.
Qed.

(* The converse of I|A is I|A itself.                                           *)
Proposition IAConverse : forall (A:Class),
  (I:|:A)^:-1: :~: (I:|:A).
Proof.
  intros A x. split; intros H1.
  - destruct H1 as [y [z [H1 H2]]].
    apply IACharac2 in H2. destruct H2 as [H2 H3]. subst.
    apply IACharac2. split. 1: assumption. reflexivity.
  - apply IACharac in H1. destruct H1 as [y [H1 H2]]. subst.
    apply Converse.Charac2Rev, IACharac2. split. 1: assumption. reflexivity.
Qed.

(* I|A is a one-to-one class.                                                   *)
Proposition IAIsOneToOne : forall (A:Class), OneToOne (I:|:A).
Proof.
  intros A. split.
  - apply IAIsFunctional.
  - apply Functional.EquivCompat with (I:|:A).
    + apply EquivSym, IAConverse.
    + apply IAIsFunctional.
Qed.

(* I|A is a bijection class.                                                    *)
Proposition IAIsBijection : forall (A:Class), Bijection (I:|:A).
Proof.
  intros A. split.
  - apply Restrict.IsRelation.
  - apply IAIsOneToOne.
Qed.


(* The domain of I|A is A.                                                      *)
Proposition IADomain : forall (A:Class), domain (I:|:A) :~: A.
Proof.
  intros A.
  apply EquivTran with (A :/\: domain I). 1: apply DomainOfRestrict.
  apply EquivTran with (A :/\: V).
  - apply Inter2.EquivCompatR, IDomain.
  - apply Inter2VR.
Qed.

(* The range of I|A is A.                                                       *)
Proposition IARange : forall (A:Class), range (I:|:A) :~: A.
Proof.
  intros A y. split; intros H1.
  - destruct H1 as [x H1]. apply IACharac2 in H1.
    destruct H1 as [H1 H2]. subst. assumption.
  - exists y. apply IACharac2. split. 1: assumption. reflexivity.
Qed.

(* I|A is a function class defined on A.                                        *)
Proposition IAIsFunctionOn : forall (A:Class), FunctionOn (I:|:A) A.
Proof.
  split.
  - apply IAIsFunction.
  - apply IADomain.
Qed.

(* I|A is a bijection class defined on A.                                       *)
Proposition IAIsBijectionOn : forall (A:Class), BijectionOn (I:|:A) A.
Proof.
  intros A. split.
  - apply IAIsBijection.
  - apply IADomain.
Qed.


(* I|A is a bijection class from A to A.                                        *)
Proposition IAIsBij : forall (A:Class), Bij (I:|:A) A A.
Proof.
  intros A. split.
  - apply IAIsBijectionOn.
  - apply IARange.
Qed.


(* If x lies in A, then the value of I|A at x is x.                             *)
Proposition IAEval : forall (A:Class) (x:U),
  A x -> (I:|:A)!x = x.
Proof.
  intros A x H1. apply eq_trans with I!x.
  - apply Restrict.Eval. 2: assumption. apply IIsFunctional.
  - apply IEval.
Qed.

(* I|A is an isomorphism class from A to A w.r to R (and R).                    *)
Proposition IAIsIsom : forall (R A:Class), Isom (I:|:A) R R A A.
Proof.
  intros R A. split.
  - apply IAIsBij.
  - intros x y H1 H2.
    assert ((I:|:A)!x = x) as H4. { apply IAEval. assumption. }
    assert ((I:|:A)!y = y) as H5. { apply IAEval. assumption. }
    split; intros H3.
    + rewrite H4, H5. assumption.
    + rewrite H4, H5 in H3. assumption.
Qed.

Proposition IAIsConverseFF : forall (F A B:Class), Bij F A B ->
  F^:-1: :.: F :~: (I:|:A).
Proof.
  intros F A B [[[H1 H2] H3] H4] u. split; intros H5.
  - destruct H5 as [x [y [z [H5 [H6 H7]]]]]. subst.
    apply Converse.Charac2 in H7.
    assert (x = z) as H8. {
      revert H7. revert H6. apply OneToOne.CharacL. assumption. }
    subst. apply IACharac2. split. 2: reflexivity. apply H3.
    exists y. assumption.
  - apply IACharac in H5. destruct H5 as [x [H5 H6]]. subst.
    apply Compose.Charac2. apply H3 in H5.
    destruct H5 as [y H5].
    exists y. split. 1: assumption. apply Converse.Charac2Rev. assumption.
Qed.

Proposition IBisFConverseF : forall (F A B:Class), Bij F A B ->
  F :.: F^:-1: :~: (I:|:B).
Proof.
  intros F A B H1. assert (H2 := H1). destruct H2 as [[[H2 _] _] _].
  apply EquivTran with ((F^:-1:)^:-1: :.: F^:-1:).
  - apply Compose.EquivCompatL, EquivSym, Converse.IsIdempotent. assumption.
  - apply IAIsConverseFF with A. apply ConverseIsBij. assumption.
Qed.
