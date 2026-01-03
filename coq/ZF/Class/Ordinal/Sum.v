Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.OrdFun.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Class.Ordinal.Recursion3.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.UnionGenOfClass.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Eval.

Module COC := ZF.Class.Ordinal.Core.
Module COR := ZF.Class.Ordinal.Recursion3.
Module SFO := ZF.Set.Relation.FunctionOn.
Module SOC := ZF.Set.Ordinal.Core.
Module SUG := ZF.Set.Ordinal.UnionGenOfClass.

Definition Oracle (F:Class) : Class := fun x => exists c a,
  x = :(:(c,a):, a :+: F!c):.

(* The unique function class G defined on On by the equations:                  *)
(* (i)    G(0)      = 0                                                         *)
(* (ii)   G(succ b) = G(b) + F(b)                                               *)
(* (iii)  G(b)      = \/_{x :< b} G(x) , if b is a limit ordinal                *)
Definition sum (F:Class) : Class := COR.Recursion (Oracle F) :0:.

Lemma OracleCharac2 : forall (F:Class) (x y:U),
  Oracle F :(x,y): <-> exists c a, x = :(c,a): /\ y = a :+: F!c.
Proof.
  intros F x y. split; intros H1.
  - destruct H1 as [c [a H1]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H2].
    exists c, a; split; assumption.
  - destruct H1 as [c [a [H1 H2]]]. exists c, a. subst. reflexivity.
Qed.

Lemma OracleCharac3 : forall (F:Class) (c a y:U),
  Oracle F :(:(c,a):,y): <-> y = a :+: F!c.
Proof.
  intros F c a y. split; intros H1.
  - destruct H1 as [c' [a' H1]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H2].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3].
    subst. reflexivity.
  - exists c, a. subst. reflexivity.
Qed.


Lemma OracleFunctional : forall (F:Class), Functional (Oracle F).
Proof.
  intros F x y1 y2 H1 H2.
  apply OracleCharac2 in H1. apply OracleCharac2 in H2.
  destruct H1 as [c [a [H1 H3]]].
  destruct H2 as [c' [a' [H2 H4]]].
  subst. apply OrdPair.WhenEqual in H2. destruct H2 as [H1 H2].
  subst. reflexivity.
Qed.

Lemma OracleEval : forall (F:Class) (c a:U),
  ((Oracle F)!:(c,a):) = a :+: F!c.
Proof.
  intros F c a.
  apply (EvalOfClass.Charac (Oracle F)).
  - apply OracleFunctional.
  - exists (a :+: F!c). apply OracleCharac3. reflexivity.
  - apply OracleCharac3. reflexivity.
Qed.

Proposition IsFunctionOn : forall (F:Class),
  FunctionOn (sum F) On.
Proof.
  intros F. apply COR.IsFunctionOn.
Qed.

Proposition WhenZero : forall (F:Class),
  (sum F)!:0: = :0:.
Proof.
  intros F. apply COR.WhenZero.
Qed.

Proposition WhenSucc : forall (F:Class) (b:U), Ordinal b ->
  (sum F)!(succ b) = (sum F)!b :+: F!b.
Proof.
  intros F b H1.
  assert ((sum F)!(succ b) = (Oracle F)!:(b,(sum F)!b):) as H2. {
    apply COR.WhenSucc. assumption. }
  rewrite OracleEval in H2. assumption.
Qed.

Proposition WhenLimit : forall (F:Class) (b:U), Limit b ->
  (sum F)!b = :\/:_{b} (sum F).
Proof.
  intros F. apply COR.WhenLimit.
Qed.

Proposition IsUnique : forall (F G:Class) (a:U),
  FunctionOn G On                                   ->
  G!:0: = :0:                                       ->  (* (i)   *)
  (forall b, Ordinal b -> G!(succ b) = G!b :+: F!b) ->  (* (ii)  *)
  (forall b, Limit b   -> G!b = :\/:_{b} G)         ->  (* (iii) *)
  G :~: sum F.
Proof.
  intros F G a H1 H2 H3. apply COR.IsUnique; try assumption.
  intros b H4. rewrite OracleEval. apply H3. assumption.
Qed.

Proposition RestrictIsFunctionOn : forall (F:Class) (b:U), On b ->
  SFO.FunctionOn (sum F :|: b) b.
Proof.
  intros F. apply COR.RestrictIsFunctionOn.
Qed.

Proposition IsOrdinal : forall (F:Class) (a:U),
  OrdFun F                          ->
  On a                              ->
  (forall x, x :< a -> domain F x)  ->
  On (sum F)!a.
Proof.
  intros F a H1. revert a.
  remember (fun a => (forall x, x :< a -> domain F x) -> On (sum F)!a) as A eqn:H2.
  assert (forall a, On a -> A a) as H3. {
    apply Induction2; rewrite H2.
    - intros _. rewrite WhenZero. apply SOC.ZeroIsOrdinal.
    - intros a H3 IH H4. rewrite WhenSucc. 2: assumption.
      apply Plus.IsOrdinal.
      + apply IH. intros x H5. apply H4. apply Succ.IsIncl. assumption.
      + apply OrdFun.IsOrdinal. 1: assumption. apply H4. apply Succ.IsIn.
    - intros a H3 IH H4.
      assert (On a) as H5. { apply H3. }
      rewrite WhenLimit. 2: assumption. apply SUG.IsOrdinal.
      intros x H6. apply IH. 1: assumption.
      intros y H7. apply H4.
      assert (On x) as H8. { apply SOC.IsOrdinal with a; assumption. }
      assert (On y) as H9. { apply SOC.IsOrdinal with x; assumption. }
      apply SOC.ElemElemTran with x; assumption. }
  rewrite H2 in H3. assumption.
Qed.

Proposition EqualCharac : forall (F G:Class) (a:U),
  On a                            ->
  (forall x, x :< a -> F!x = G!x) ->
  (sum F)!a = (sum G)!a.
Proof.
  intros F G.
  remember (fun a =>
    (forall x, x :< a -> F!x = G!x) -> (sum F)!a = (sum G)!a) as A eqn:H1.
  assert (forall a, On a -> A a) as H2. {
    apply Induction2; rewrite H1.
    - intros _. rewrite WhenZero, WhenZero. reflexivity.
    - intros a H2 IH H3.
      rewrite WhenSucc, WhenSucc; try assumption.
      assert ((sum F)!a = (sum G)!a) as H4. {
        apply IH. intros x H4. apply H3. apply Succ.IsIncl. assumption. }
      assert (F!a = G!a) as H5. { apply H3. apply Succ.IsIn. }
      rewrite H4, H5. reflexivity.
    - intros a H2 IH H3.
      rewrite WhenLimit, WhenLimit; try assumption.
      apply SUG.EqualCharac. intros x H4.
      apply IH. 1: assumption. intros y H5. apply H3.
      assert (Ordinal a) as G1. { apply H2. }
      assert (Ordinal x) as G2. { apply SOC.IsOrdinal with a; assumption. }
      assert (Ordinal y) as G3. { apply SOC.IsOrdinal with x; assumption. }
      apply SOC.ElemElemTran with x; assumption. }
  rewrite H1 in H2. assumption.
Qed.
