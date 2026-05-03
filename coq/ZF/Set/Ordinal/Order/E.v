Require Import ZF.Axiom.Foundation.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Restrict.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Specify.
Require Import ZF.Set.Order.Founded.
Require Import ZF.Set.Order.Irreflexive.
Require Import ZF.Set.Order.RestrictOfClass.
Require Import ZF.Set.Order.StrictOrd.
Require Import ZF.Set.Order.StrictTotalOrd.
Require Import ZF.Set.Order.Total.
Require Import ZF.Set.Order.Transitive.
Require Import ZF.Set.Order.WellOrdering.

Module COE := ZF.Class.Order.E.

(* The binary relation on a induced by :<.                                      *)
Definition E (a:U) : U := {{ x :< a :x: a | COE.E }}.

Proposition Charac : forall (a x:U),
  x :< (E a) <-> exists y z, x = :(y,z): /\ y :< a /\ z :< a /\ y :< z.
Proof.
  intros a x. split; intros H1.
  - apply Specify.Charac in H1. destruct H1 as [H1 H2].
    apply Prod.Charac in H1. destruct H1 as [y [z [H1 [H3 H4]]]].
    subst. apply COE.Charac2 in H2. exists y. exists z.
    split. 1: reflexivity. split. 1: assumption. split; assumption.
  - destruct H1 as [y [z [H1 [H2 [H3 H4]]]]]. subst.
    apply Specify.Charac. split.
    + apply Prod.Charac2. split; assumption.
    + apply COE.Charac2. assumption.
Qed.

Proposition Charac2 : forall (a y z:U),
  :(y,z): :< (E a) <-> y :< a /\ z :< a /\ y :< z.
Proof.
  intros a y z. split; intros H1.
  - apply Charac in H1. destruct H1 as [y' [z' [H1 [H2 [H3 H4]]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H5]. subst.
    split. 1: assumption. split; assumption.
  - apply Charac. exists y. exists z. split. 1: reflexivity. assumption.
Qed.

Proposition ToClass : forall (a:U),
  toClass (E a) :~: COE.E:/:(toClass a).
Proof.
apply RestrictOfClass.ToClass.
Qed.

(* The relation E a is irreflexive on a.                                        *)
Proposition IsIrreflexive : forall (a:U),
  Irreflexive (E a) a.
Proof.
  (* Proof by Claude.                                                           *)
  intros a x _ H1. apply Charac2 in H1. destruct H1 as [_ [_ H1]].
  revert H1. apply NoElemLoop1.
Qed.

(* The relation E a is transitive on the ordinal a.                             *)
Proposition IsTransitive : forall (a:U), Ordinal a ->
  Transitive (E a) a.
Proof.
  (* Proof by Claude.                                                           *)
  intros a H1 x y z H2 H3 H4 H5 H6.
  apply Charac2 in H5. destruct H5 as [_ [_ H5]].
  apply Charac2 in H6. destruct H6 as [_ [_ H6]].
  apply Charac2. split. 1: assumption. split. 1: assumption.
  apply ElemElemTran with y; try assumption.
  - apply IsOrdinal with a; assumption.
  - apply IsOrdinal with a; assumption.
  - apply IsOrdinal with a; assumption.
Qed.

(* The relation E a is total on the ordinal a.                                  *)
Proposition IsTotal : forall (a:U), Ordinal a ->
  Total (E a) a.
Proof.
  (* Proof by Claude.                                                           *)
  intros a H1 x y H2 H3.
  assert (x = y \/ x :< y \/ y :< x) as H4. {
    apply ZF.Set.Ordinal.Core.IsTotal.
    - apply IsOrdinal with a; assumption.
    - apply IsOrdinal with a; assumption. }
  destruct H4 as [H4|[H4|H4]].
  - left. assumption.
  - right. left. apply Charac2. split. 1: assumption. split; assumption.
  - right. right. apply Charac2. split. 1: assumption. split; assumption.
Qed.

(* The relation E a is founded on a.                                            *)
Proposition IsFounded : forall (a:U),
  Founded (E a) a.
Proof.
  (* Proof by Claude.                                                           *)
  intros a b _ H2.
  destruct (Foundation b H2) as [x [H3 H4]].
  exists x. split. 1: assumption.
  intros y H5 H6.
  apply Charac2 in H6. destruct H6 as [_ [_ H6]].
  assert (y :< x :/\: b) as H7. {
    apply Inter2.Charac. split; assumption. }
  rewrite H4 in H7. apply Empty.Charac in H7. exact H7.
Qed.

(* The relation E a is a strict order on the ordinal a.                         *)
Proposition IsStrictOrd : forall (a:U), Ordinal a ->
  StrictOrd (E a) a.
Proof.
  (* Proof by Claude.                                                           *)
  intros a H1. split.
  - apply IsIrreflexive.
  - apply IsTransitive. assumption.
Qed.

(* The relation E a is a strict total order on the ordinal a.                  *)
Proposition IsStrictTotalOrd : forall (a:U), Ordinal a ->
  StrictTotalOrd (E a) a.
Proof.
  (* Proof by Claude.                                                           *)
  intros a H1. split.
  - apply IsStrictOrd. assumption.
  - apply IsTotal. assumption.
Qed.

(* The relation E a is a well-ordering on the ordinal a.                       *)
Proposition IsWellOrdering : forall (a:U), Ordinal a ->
  WellOrdering (E a) a.
Proof.
  (* Proof by Claude.                                                           *)
  intros a H1. split.
  - apply IsFounded.
  - apply IsTotal. assumption.
Qed.
