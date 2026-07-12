Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.OrdFun.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.ImageUnderClass.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Single.

Module COC := ZF.Class.Ordinal.Core.
Module COO := ZF.Class.Ordinal.OrdFun.
Module CRD := ZF.Class.Relation.Domain.

(* An ordinal function is a function with ordinal domain and ordinal values.    *)
Definition OrdFun : Class := fun f =>
  Function f                              /\
  Ordinal (domain f)                      /\
  (forall y, y :< range f -> Ordinal y).

(* If the set is an ordinal function, then so is the class.                     *)
Proposition ToClass : forall (f:U),
  OrdFun f -> COO.OrdFun (toClass f).
Proof.
  intros f [H1 [H2 H3]]. split.
  - apply Function.ToClass. assumption.
  - split.
    + apply COC.EquivCompat with (toClass (domain f)).
      * apply Domain.ToClass.
      * apply Core.ToClass. assumption.
    + intros y H4. apply H3. apply Range.ToClass. assumption.
Qed.

(* If the class is an ordinal function, then so is the set.                     *)
Proposition FromClass : forall (f:U),
  COO.OrdFun (toClass f) -> OrdFun f.
Proof.
  intros f [H1 [H2 H3]]. split.
  - apply Function.FromClass. assumption.
  - split.
    + apply Core.FromClass. apply COC.EquivCompat with (CRD.domain (toClass f)).
      2: assumption. apply Equiv.Sym, Domain.ToClass.
    + intros y H4. apply H3. apply Range.ToClass. assumption.
Qed.

(* Restricting a class ordinal function to an ordinal is an ordinal function.   *)
Proposition ClassRestrict : forall (F:Class) (a:U),
  Ordinal a                     ->
  COO.OrdFun F                  ->
  toClass a :<=: CRD.domain F   ->
  OrdFun (F:|:a).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros F a H1 [H2 [H3 H4]] H5.
  assert (FunctionOn (F:|:a) a) as H6. {
    apply RestrictOfClass.IsFunctionOn. 1: apply H2. assumption. }
  split. 1: apply H6. split.
  - (* Its set-theoretic domain is exactly that ordinal.                        *)
    assert (domain (F:|:a) = a) as H7. { apply H6. }
    rewrite H7. assumption.
  - intros y H7.
    (* Its values are values of the original class ordinal function.            *)
    rewrite RestrictOfClass.RangeOf in H7. 2: apply H2.
    apply ImageUnderClass.Charac in H7. 2: apply H2.
    destruct H7 as [x [H7 H8]]. apply H4. exists x. assumption.
Qed.

(* The value of an ordinal function at any domain element is an ordinal.        *)
Proposition IsOrdinal : forall (f x:U), OrdFun f ->
  x :< domain f -> Ordinal f!x.
Proof.
  intros f x [H1 [H2 H3]] H4. assert (H5 := H4).
  apply Domain.Charac in H5. destruct H5 as [y H5].
  assert (f!x = y) as H6. { apply Eval.Charac; try assumption. apply H1. }
  rewrite H6. apply H3. apply Range.Charac. exists x. assumption.
Qed.

(* The domain of an ordinal function is an ordinal.                             *)
Proposition DomainOf : forall (f:U),
  OrdFun f -> Ordinal (domain f).
Proof.
  intros f [_ [H1 _]]. assumption.
Qed.

(* The empty set is an ordinal function.                                        *)
Proposition WhenZero : forall (f:U),
  f = :0: -> OrdFun f.
Proof.
  intros f H1. split.
  - apply Function.WhenZero. assumption.
  - split.
    + assert (domain f = :0:) as H2. { apply Domain.WhenZero. assumption. }
      rewrite H2. apply Core.Zero.
    + intros y H2.
      assert (range f = :0:) as H3. { apply Range.WhenZero. assumption. }
      rewrite H3 in H2. apply Empty.Charac in H2. contradiction.
Qed.

(* The singleton of the pair (0,a) is an ordinal function when a is ordinal.    *)
Proposition WhenSingle : forall (a f:U),
  Ordinal a           ->
  f = :{ :(:0:,a): }: ->
  OrdFun f.
Proof.
  intros a f H1 H2. split.
  - apply Function.WhenSingle with :0: a. assumption.
  - split.
    + rewrite Domain.WhenSingle with :0: a f. 2: assumption.
      rewrite <- Natural.OneExtension. apply Natural.OneIsOrdinal.
    + intros y H3. rewrite Range.WhenSingle with :0: a f in H3.
      2: assumption. apply Single.Charac in H3. subst. assumption.
Qed.
