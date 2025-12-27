Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Recursion2.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Relation.ToFun.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Mult.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Eval.

Module CFO := ZF.Class.Relation.FunctionOn.
Module SOC := ZF.Set.Ordinal.Core.
Module SUG := ZF.Set.UnionGenOfClass.

(* Not quite the function class (a ^ .) when a is an ordinal: because 0^0 is    *)
(* defined as 1, setting a^b = \/_{c :< b} a^c for limit ordinal b implies that *)
(* 0^b = 1 for b limit ordinal since 0 :< b. This is not what we want. We want  *)
(* 0^b = 0 whenever 1 <= b.                                                     *)
Definition Exp' (a:U) : Class := Recursion :[fun b => b :*: a]: :1:.

(* The function class F such that F(0) = 1 and F(x) = 0 for 0 < x.              *)
Definition OnZero : Class := fun x => exists y z,
  x = :(y,z):               /\
  On y                      /\
  ((y  = :0:  /\ z = :1:)   \/
   (:0: :< y  /\ z = :0:)).

(* The function class (a ^ .) when a is an ordinal.                             *)
Definition Exp (a:U) : Class := fun x =>
  (a = :0: /\ OnZero x) \/ (a <> :0: /\ Exp' a x).

Proposition OnZeroCharac2 : forall (x y:U),
  OnZero :(x,y): <-> On x /\ ((x = :0: /\ y = :1:) \/ (:0: :< x /\ y = :0:)).
Proof.
  intros x y. split; intros H1.
  - destruct H1 as [x' [y' [H1 [H2 H3]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H4]. subst.
    split; assumption.
  - destruct H1 as [H1 [[H2 H3]|[H2 H3]]]; subst.
    + exists :0:. exists :1:. split. 1: reflexivity. split. 1: assumption.
      left. split; reflexivity.
    + exists x. exists :0:. split. 1: reflexivity. split. 1: assumption.
      right. split. 1: assumption. reflexivity.
Qed.

Proposition WhenZeroCharac2 : forall (a y z:U), a = :0: ->
  Exp a :(y,z): <-> OnZero :(y, z):.
Proof.
  intros a y z H1. split; intros H2.
  - destruct H2 as [[_ H2]|[H2 _]]. 1: assumption. contradiction.
  - left. split; assumption.
Qed.

Proposition WhenNotZeroCharac2 : forall (a y z:U), a <> :0: ->
  Exp a :(y,z): <-> Exp' a :(y,z):.
Proof.
  intros a y z H1. split; intros H2.
  - destruct H2 as [[H2 _]|[_ H2]]. 1: contradiction. assumption.
  - right. split; assumption.
Qed.

Proposition WhenZeroL : forall (a:U),
  a = :0: -> Exp a :~: OnZero.
Proof.
  intros a H1 x. split; intros H2.
  - destruct H2 as [[H2 H3]|[H2 H3]]. 1: assumption. contradiction.
  - left. split; assumption.
Qed.

Proposition WhenNotZeroL : forall (a:U),
  a <> :0: -> Exp a :~: Exp' a.
Proof.
  intros a H1 x. split; intros H2.
  - destruct H2 as [[H2 H3]|[H2 H3]]. 2: assumption. contradiction.
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

Proposition OnZeroIsFunctional : Functional OnZero.
Proof.
  intros x y1 y2 H1 H2.
  apply OnZeroCharac2 in H1. apply OnZeroCharac2 in H2.
  destruct H1 as [H1 H3]. destruct H2 as [_ H2].
  destruct H3 as [[H3 H4]|[H3 H4]]; destruct H2 as [[H2 H5]|[H2 H5]]; subst;
  try reflexivity.
  - apply Empty.Charac in H2. contradiction.
  - apply Empty.Charac in H3. contradiction.
Qed.

Proposition IsFunctional : forall (a:U), Functional (Exp a).
Proof.
  intros a x y1 y2 H1 H2.
  destruct H1 as [[H1 H3]|[H1 H3]];
  destruct H2 as [[H2 H4]|[H2 H4]]; try contradiction.
  - apply OnZeroCharac2 in H3. apply OnZeroCharac2 in H4.
    destruct H3 as [H3 [[H5 H6]|[H5 H6]]];
    destruct H4 as [H4 [[H7 H8]|[H7 H8]]]; subst; try reflexivity.
    + apply Empty.Charac in H7. contradiction.
    + apply Empty.Charac in H5. contradiction.
  - assert (Functional (Exp' a)) as H5. { apply IsFunctionOn'. }
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
    + destruct H2 as [y H2].
      apply WhenZeroCharac2 in H2. 2: reflexivity.
      apply OnZeroCharac2 in H2. apply H2.
    + assert (x = :0: \/ :0: :< x) as H3. { apply Core.ZeroOrElem. assumption. }
      destruct H3 as [H3|H3].
      * subst. exists :1:. apply WhenZeroCharac2. 1: reflexivity.
        apply OnZeroCharac2. split. 1: assumption. left. split; reflexivity.
      * exists :0:. apply WhenZeroCharac2. 1: reflexivity.
        apply OnZeroCharac2. split. 1: assumption. right.
        split. 1: assumption. reflexivity.
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

Proposition WhenZero : forall (a:U), (Exp a)!:0: = :1:.
Proof.
  intros a.
  assert (a = :0: \/ a <> :0:) as H1. { apply LawExcludedMiddle. }
  destruct H1 as [H1|H1].
  - assert (Exp a :~: OnZero) as H2. { apply WhenZeroL. assumption. }
    rewrite (EvalOfClass.EquivCompat (Exp a) OnZero). 2: assumption.
    apply EvalOfClass.Charac.
    + apply OnZeroIsFunctional.
    + exists :1:. apply OnZeroCharac2. split.
      * apply SOC.ZeroIsOrdinal.
      * left. split; reflexivity.
    + apply OnZeroCharac2. split.
      * apply SOC.ZeroIsOrdinal.
      * left. split; reflexivity.
  - assert (Exp a :~: Exp' a) as H2. { apply WhenNotZeroL. assumption. }
    rewrite (EvalOfClass.EquivCompat (Exp a) (Exp' a)). 2: assumption.
    apply Recursion2.WhenZero.
Qed.

Proposition WhenSucc : forall (a b:U), On b ->
  (Exp a)!(succ b) = (Exp a)!b :*: a.
Proof.
  intros a b H1.
  assert (a = :0: \/ a <> :0:) as H2. { apply LawExcludedMiddle. }
  destruct H2 as [H2|H2].
  - assert (Exp a :~: OnZero) as H3. { apply WhenZeroL. assumption. }
    rewrite (EvalOfClass.EquivCompat (Exp a) OnZero). 2: assumption.
    rewrite (EvalOfClass.EquivCompat (Exp a) OnZero). 2: assumption.
    subst. rewrite Mult.WhenZeroR. apply EvalOfClass.Charac.
    + apply OnZeroIsFunctional.
    + exists :0:. apply OnZeroCharac2. split.
      * apply Succ.IsOrdinal. assumption.
      * right. split. 2: reflexivity. apply Succ.HasZero. assumption.
    + apply OnZeroCharac2. split.
      * apply Succ.IsOrdinal. assumption.
      * right. split. 2: reflexivity. apply Succ.HasZero. assumption.
  - assert (Exp a :~: Exp' a) as H3. { apply WhenNotZeroL. assumption. }
    rewrite (EvalOfClass.EquivCompat (Exp a) (Exp' a)). 2: assumption.
    rewrite (EvalOfClass.EquivCompat (Exp a) (Exp' a)). 2: assumption.
    rewrite <- (ToFun.Eval (fun b => b :*: a)).
    apply Recursion2.WhenSucc. assumption.
Qed.

Proposition WhenLimitZero : forall (a b:U), Limit b ->
  a = :0: -> (Exp a)!b = :0:.
Proof.
  intros a b H1 H2.
  assert (Exp a :~: OnZero) as H3. { apply WhenZeroL. assumption. }
  rewrite (EvalOfClass.EquivCompat (Exp a) OnZero). 2: assumption.
  apply EvalOfClass.Charac.
  - apply OnZeroIsFunctional.
  - exists :0:. apply OnZeroCharac2. split.
    + apply H1.
    + right. split. 2: reflexivity. apply Limit.HasZero. assumption.
  - apply OnZeroCharac2. split.
    + apply H1.
    + right. split. 2: reflexivity. apply Limit.HasZero. assumption.
Qed.

Proposition WhenLimit : forall (a b:U), Limit b ->
  a <> :0: -> (Exp a)!b = :\/:_{b} (Exp a).
Proof.
  intros a b H1 H2.
  assert (Exp a :~: Exp' a) as H3. { apply WhenNotZeroL. assumption. }
  rewrite (EvalOfClass.EquivCompat (Exp a) (Exp' a)). 2: assumption.
  rewrite (SUG.EquivCompat (Exp a) (Exp' a)). 2: assumption.
  apply Recursion2.WhenLimit. assumption.
Qed.
