Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Class.Ordinal.OrdFun.
Require Import ZF.Class.Ordinal.Recursion2.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.UnionGenOfClass.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Module COC := ZF.Class.Ordinal.Core.
Module CRF := ZF.Class.Relation.Function.

Module SOC := ZF.Set.Ordinal.Core.

(* A strictly monotone ordinal function.                                        *)
Definition Monotone (F:Class) : Prop := OrdFun F /\ forall (a b:U),
  domain F a -> domain F b -> a :< b -> F!a :< F!b.

Proposition IsIncl : forall (F:Class) (a:U),
  Monotone F -> domain F a -> a :<=: F!a.
Proof.
  intros F a [[H1 [H2 H3]] H4] H5.
  assert (On a) as H6. {
    apply COC.IsOrdinal with (domain F); assumption. }
  assert (On (F!a)) as H7. { apply H3, CRF.IsInRange; assumption. }
  remember (fun b => domain F b /\ F!b :< b) as A eqn:H8.
  assert (A :~: :0: \/ A :<>: :0:) as H9. { apply LawExcludedMiddle. }
  destruct H9 as [H9|H9].
  - assert (F!a :< a \/ a :<=: F!a) as H10. { apply SOC.ElemOrIncl; assumption. }
    destruct H10 as [H10|H10]. 2: assumption. exfalso.
    assert (A a) as H11. { rewrite H8. split; assumption. }
    apply H9 in H11. contradiction.
  - exfalso.
    assert (A :<=: On) as H10. {
      intros b H10. rewrite H8 in H10. apply COC.IsOrdinal with (domain F).
      1: assumption. apply H10. }
    assert (exists b, A b /\ A :/\: toClass b :~: :0:) as H11. {
      apply COC.HasEMinimal with On; try assumption. apply COC.OnIsOrdinal. }
    destruct H11 as [b [H11 H12]]. rewrite H8 in H11. destruct H11 as [H11 H13].
    assert (domain F (F!b)) as H14. {
      assert (Transitive (domain F)) as H14. { apply H2. }
      apply (H14 b); assumption. }
    assert (F!(F!b) :< F!b) as H15. { apply H4; assumption. }
    assert ((A :/\: toClass b) F!b) as H16. {
      split. 2: assumption. rewrite H8. split; assumption. }
    apply H12 in H16. contradiction.
Qed.

(* ERROR: See page 50, exercise (2). The assumption a :< F!a is necessary.      *)
(* The condition b :< F!b for all b appears to be sufficient.                   *)
Proposition FromRecursion : forall (F:Class) (a:U),
  On a                            ->
  (forall b, On b ->  b :< F!b)   ->
  Monotone F                      ->
  domain F :~: On                 ->
  Monotone (Recursion F a).
Proof.
  intros F a H1 H2 [H3 H4] H5.
  assert (OrdFun (Recursion F a)) as H6. {
    apply OrdFun.FromRecursion; assumption. }
  split. 1: assumption.
  assert (domain (Recursion F a) :~: On) as H7. { apply Recursion2.IsFunctionOn. }
  intros b c H8 H9. apply H7 in H8. apply H7 in H9. revert c H9 b H8.
  remember (fun c => forall b, On b ->
    b :< c -> (Recursion F a)!b :< (Recursion F a)!c) as A eqn:H10.
  assert (forall c, On c -> A c) as H11. {
    apply Induction2; rewrite H10.
    - intros b H11 H12. apply Empty.Charac in H12. contradiction.
    - intros c H11 H12 b H13 H14. rewrite Recursion2.WhenSucc. 2: assumption.
      assert (Ordinal (Recursion F a)!b) as H15. {
        apply H6, CRF.IsInRange. 1: apply H6. apply H7. assumption. }
      assert (Ordinal (Recursion F a)!c) as H16. {
        apply H6, CRF.IsInRange. 1: apply H6. apply H7. assumption. }
      apply Union2.Charac in H14. destruct H14 as [H14|H14].
      + apply SOC.ElemInclTran with (Recursion F a)!c; try assumption.
        * apply H3, CRF.IsInRange. 1: apply H3. apply H5. assumption.
        * apply H12; assumption.
        * apply IsIncl. { split; assumption. } { apply H5. assumption. }
      + apply Single.Charac in H14. subst. apply H2. assumption.
    - intros c H11 H12 b H13 H14. rewrite (Recursion2.WhenLimit F a c).
      2: assumption.
      assert (exists d, b :< d /\ d :< c) as H15. {
        apply Limit.InBetween; assumption. }
      destruct H15 as [d [H15 H16]].
      apply SOC.ElemInclTran with (Recursion F a)!d.
      + apply H6, CRF.IsInRange. 1: apply H6. apply H7. assumption.
      + apply H6, CRF.IsInRange. 1: apply H6. apply H7.
        apply SOC.IsOrdinal with c. 2: assumption. apply H11.
      + apply UnionGenOfClass.IsOrdinal. intros x H17.
        apply H6, CRF.IsInRange. 1: apply H6. apply H7.
        apply SOC.IsOrdinal with c. 2: assumption. apply H11.
      + apply H12; assumption.
      + apply UnionGenOfClass.IsIncl. assumption. }
  rewrite H10 in H11. assumption.
Qed.

Proposition FromIsom : forall (F A B:Class),
  Isom F E E A B  ->
  COC.Ordinal A   ->
  B :<=: On       ->
  Monotone F.
Proof.
  intros F A B [H1 H2] H3 H4. split.
  - split.
    + split; apply H1. 
    + split. apply COC.EquivCompat with A. 2: assumption.
      * apply Equiv.Sym, H1.
      * apply Incl.EquivCompatL with B. 2: assumption.
        apply Equiv.Sym, H1.
  - assert (domain F :~: A) as H5. { apply H1. }
    intros a b H6 H7 H8.  apply E.Charac2. apply H5 in H6. apply H5 in H7.
    specialize (H2 a b H6 H7). destruct H2 as [H2 H9]. apply H2, E.Charac2.
    assumption.
Qed.
