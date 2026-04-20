Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Induction.
Require Import ZF.Class.Ordinal.R1.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Fun.From.
Require Import ZF.Class.V.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.Union.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Power.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.
Require Import ZF.Set.Union.

Require Import ZF.Notation.Eval.

Module CEM := ZF.Class.Empty.
Module CIN := ZF.Class.Incl.
Module CRF := ZF.Class.Relation.Function.
Module SOI := ZF.Set.Ordinal.InfOfClass.
Module SOU := ZF.Set.Ordinal.Union.
Module SRI := ZF.Set.Relation.ImageByClass.

(* Precicate defining a well founded set.                                       *)
Definition WellFounded (a:U) : Prop := exists b, Ordinal b /\ a :< R1!b.

(* When all elements are well founded, the set is well founded.                 *)
Proposition WhenElems : forall (a:U),
  (forall x, x :< a -> WellFounded x) -> WellFounded a.
Proof.
  intros a H1.
  remember (fun x => fun b => Ordinal b /\ x :< R1!b) as A eqn:H2.
  remember (:[fun x => inf (A x)]:) as F eqn:H3.
  assert (Functional F) as G1. { rewrite H3. apply From.IsFunctional. }
  assert (Function F) as G2. { rewrite H3. apply From.IsFunction. }
  assert (toClass F:[a]: :<=: Ordinal) as H4. {
    intros b H4. apply SRI.ToClass in H4. 2: assumption.
    destruct H4 as [x [H4 H5]]. rewrite H3 in H5.
    apply From.Charac2 in H5. rewrite H5. apply SOI.IsOrdinal. }
  assert (Ordinal :U(F:[a]:)) as H6. { apply SOU.IsOrdinal. assumption. }
  remember (succ :U(F:[a]:)) as b eqn:H7.
  assert (Ordinal b) as H8. {
    rewrite H7. apply Succ.IsOrdinal. assumption. }
  assert (forall x, x :< a -> Ordinal F!x) as H9. {
    intros x H9. rewrite H3, From.Eval. apply SOI.IsOrdinal. }
  assert (forall x, x :< a -> F!x :< b) as H10. {
    intros x H10. rewrite H7. apply Succ.InclIsElem. 2: assumption.
    - apply H9. assumption.
    - apply SOU.IsUpperBound. 1: assumption.
      apply SRI.CharacRev with x; try assumption.
      apply CRF.Satisfies. 1: assumption. rewrite H3. apply From.DomainOf. }
  assert (forall x, x :< a -> R1!(F!x) :<=: R1!b) as H11. {
    intros x H11. apply R1.InclCompat. 2: assumption.
    - apply H9. assumption.
    - apply Core.ElemIsIncl. 1: assumption. apply H10. assumption. }
  assert (forall x, x :< a -> A x (inf (A x))) as H12. {
    intros x H12. apply SOI.IsIn.
    - rewrite H2. intros u [H13 H14]. assumption.
    - apply CEM.HasElem. rewrite H2. apply H1. assumption. }
  assert (forall x, x :< a -> A x F!x) as H13. {
    intros x H13. rewrite H3, From.Eval. apply H12. assumption. }
  assert (forall x, x :< a -> x :< R1!(F!x)) as H14. {
    intros x H14. rewrite H2 in H13. apply H13. assumption. }
  assert (forall x, x :< a -> x :< R1!b) as H15. {
    intros x H15. apply (H11 x). 1: assumption. apply H14. assumption. }
  assert (a :<=: R1!b) as H16. { intros x H16. apply H15. assumption. }
  assert (a :< R1!(succ b)) as H17. {
    rewrite R1.WhenSucc. 2: assumption. apply Power.Charac. assumption. }
  assert (Ordinal (succ b)) as H18. { apply Succ.IsOrdinal. assumption. }
  exists (succ b). split; assumption.
Qed.

(* Every set is well founded.                                                   *)
Proposition IsWellFounded : forall (a:U), WellFounded a.
Proof.
  assert (forall a, V a -> WellFounded a) as H1. {
    apply Induction.Induction with E.
    - apply E.IsWellFounded.
    - intros a _ IH. apply WhenElems. intros x H1. apply IH.
      rewrite InitSegment.EV. assumption. }
  intros a. apply H1, I.
Qed.

