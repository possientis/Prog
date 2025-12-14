Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.MultA.
Require Import ZF.Class.Ordinal.Recursion2.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.OrdPair.

Module CFO := ZF.Class.Relation.FunctionOn.
Module SOC := ZF.Set.Ordinal.Core.

(* Not quite the function class (a ^ .) when a is an ordinal: because 0^0 is    *)
(* defined as 1, setting a^b = \/_{c :< b} a^c for limit ordinal b implies that *)
(* 0^b = 1 for b limit ordinal since 0 :< b. This is not what we want. We want  *)
(* 0^b = 0 whenever 1 <= b.                                                     *)
Definition Exp' (a:U) : Class := Recursion (MultA a) :1:.

(* The function class F such that F(0) = 1 and F(x) = 0 for 0 < x.              *)
Definition OnZero : Class := fun x => exists y z,
  x = :(y,z):               /\
  On y                      /\
  ((y  = :0:  /\ z = :1:)   \/
   (:0: :< y  /\ z = :0:)).

(* The function class (a ^ .) when a is an ordinal.                             *)
Definition Exp (a:U) : Class := fun x =>
  (a = :0: /\ OnZero x) \/ (a <> :0: /\ Exp' a x).

Proposition OnZeroCharac2 : forall (y z:U),
  OnZero :(y,z): <-> On y /\ ((y = :0: /\ z = :1:) \/ (:0: :< y /\ z = :0:)).
Proof.
  intros y z. split; intros H1.
  - destruct H1 as [y' [z' [H1 [H2 H3]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H4]. subst.
    split; assumption.
  - destruct H1 as [H1 [[H2 H3]|[H2 H3]]]; subst.
    + exists :0:. exists :1:. split. 1: reflexivity. split. 1: assumption.
      left. split; reflexivity.
    + exists y. exists :0:. split. 1: reflexivity. split. 1: assumption.
      right. split. 1: assumption. reflexivity.
Qed.

Proposition WhenZeroCharac2 : forall (y z:U),
  Exp :0: :(y,z): <-> On y /\ ((y = :0: /\ z = :1:) \/ (:0: :< y /\ z = :0:)).
Proof.
  intros y z. split; intros H1.
  - destruct H1 as [[_ H1]|[H1 _]].
    + apply OnZeroCharac2 in H1. assumption.
    + exfalso. apply H1. reflexivity.
  - left. split. 1: reflexivity. apply OnZeroCharac2. assumption.
Qed.

Proposition WhenNotZeroCharac2 : forall (a y z:U), a <> :0: ->
  Exp a :(y,z): <-> Exp' a :(y,z):.
Proof.
  intros a y z H1. split; intros H2.
  - destruct H2 as [[H2 _]|[_ H2]]. 1: contradiction. assumption.
  - right. split; assumption.
Qed.

Proposition IsFunctionOn' : forall (a:U), CFO.FunctionOn (Exp' a) On.
Proof.
  intros a. apply Recursion2.IsFunctionOn.
Qed.

Proposition IsRelation : forall (a:U), Relation (Exp a).
Proof.
  intros a x [[H1 H2]|[H1 H2]].
  - destruct H2 as [y [z [H2 _]]]. exists y. exists z. assumption.
  - assert (Relation (Exp' a)) as H3. { apply IsFunctionOn'. }
    apply H3. assumption.
Qed.

Proposition IsFunctional : forall (a:U), Functional (Exp a).
Proof.
  intros a x y1 y2 H1 H2.
  assert (a = :0: \/ a <> :0:) as H3. { apply LawExcludedMiddle. }
  destruct H3 as [H3|H3].
  - subst. apply WhenZeroCharac2 in H1. apply WhenZeroCharac2 in H2.
    destruct H1 as [_ [[H1i H3]|[H1 H3]]]; destruct H2 as [_ [[H2 H4]|[H2 H4]]];
    subst; try reflexivity.
    + apply Empty.Charac in H2. contradiction.
    + apply Empty.Charac in H1. contradiction.
  - apply WhenNotZeroCharac2 in H1. 2: assumption.
    apply WhenNotZeroCharac2 in H2. 2: assumption.
    assert (Functional (Exp' a)) as H5. { apply IsFunctionOn'. }
    apply H5 with x; assumption.
Qed.

Proposition IsFunction : forall (a:U), Function (Exp a).
Proof.
  intros a. split.
  - apply IsRelation.
  - apply IsFunctional.
Qed.

Proposition DomainOf : forall (a:U), domain (Exp a) :~: On.
Proof.
  intros a.
  assert (a = :0: \/ a <> :0:) as H1. { apply LawExcludedMiddle. }
  destruct H1 as [H1|H1]; intros x.
  - subst. split; intros H2.
    + destruct H2 as [y H2]. apply WhenZeroCharac2 in H2. apply H2.
    + assert (x = :0: \/ :0: :< x) as H3. { apply Core.ZeroOrElem. assumption. }
      destruct H3 as [H3|H3].
      * subst. exists :1:. apply WhenZeroCharac2. split. 1: assumption.
        left. split; reflexivity.
      * exists :0:. apply WhenZeroCharac2. split. 1: assumption.
        right. split. 1: assumption. reflexivity.
  - assert (domain (Exp' a) :~: On) as H3. { apply IsFunctionOn'. }
    split; intros H2.
    + destruct H2 as [ y H2]. apply WhenNotZeroCharac2 in H2. 2: assumption.
      apply H3. exists y. assumption.
    + apply H3 in H2. destruct H2 as [y H2]. exists y.
      apply WhenNotZeroCharac2; assumption.
Qed.

Proposition IsFunctionOn : forall (a:U), CFO.FunctionOn (Exp a) On.
Proof.
  intros a. split.
  - apply IsFunction.
  - apply DomainOf.
Qed.
