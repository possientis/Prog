Require Import ZF.Class.
Require Import ZF.Class.Ordinal.
Require Import ZF.Class.Union.
Require Import ZF.Set.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Singleton.
Require Import ZF.Set.Union2.

Definition succ (a:U) : U := a :\/: :{a}:.

(* The successor of an ordinal is an ordinal.                                   *)
Proposition SuccIsOrdinal : forall (a:U), Ordinal a ->
  Ordinal (succ a).
Proof.
  intros a H1. split.
  - intros x H2 y H3. apply Union2Charac in H2.
    apply Union2Charac. destruct H2 as [H2|H2].
    + left. destruct H1 as [H1 _]. specialize (H1 x H2 y). apply H1. assumption.
    + apply SingleCharac in H2. subst. left. assumption.
  - intros x y H2 H3. apply Union2Charac in H2. apply Union2Charac in H3.
    destruct H2 as [H2|H2]; destruct H3 as [H3|H3].
    + destruct H1 as [_ H1]. apply H1; assumption.
    + apply SingleCharac in H3. subst. right. left. assumption.
    + apply SingleCharac in H2. subst. right. right. assumption.
    + apply SingleCharac in H2. apply SingleCharac in H3. 
      subst. left. apply eq_refl.
Qed.

(* The union of the class of ordinals is the class of ordinals.                 *)
Proposition UnionOfOn : :U(On) :~: On.
Proof.
  apply Class.Incl.DoubleInclusion. split.
  - apply Transitive2.UnionIncl, OnIsOrdinal.
  - intros a H1. exists (a :\/: :{a}:). split.
    + apply Union2Charac. right. apply SingleIn.
    + apply SuccIsOrdinal. assumption.
Qed.

(* A set (ordinal or not) belongs to its successor.                             *)
Proposition ElemSucc : forall (a:U), a :< succ a.
Proof.
  intros a. apply Union2Charac. right. apply SingleIn.
Qed.

(* A set (ordinal or not) is a subset of its successor.                         *)
Proposition InclSucc : forall (a:U), a :<=: succ a.
Proof.
  intros a.  apply Union2InclL.
Qed.

(* The sets a and b need not be ordinals.                                       *)
Proposition NothingInBetween : forall (a b:U),
  ~ (a :< b /\ b :< succ a).
Proof.
  intros a b [H1 H2]. apply Union2Charac in H2. destruct H2 as [H2|H2].
  - apply NoElemLoop2 with a b. split; assumption.
  - apply SingleCharac in H2. subst. apply NoElemLoop1 with a. assumption.
Qed.


