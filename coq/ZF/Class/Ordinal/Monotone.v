Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.OrdFun.
Require Import ZF.Class.Ordinal.Recursion2.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Relation.EvalOfClass.

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

Proposition RecursionMonotone : forall (F:Class) (a:U),
  On a                      ->
  Monotone F                ->
  domain F :~: On           ->
  Monotone (Recursion F a).
Proof.
  intros F a H1 [[H2 [H3 H4]] H5] H6.
  assert (domain (Recursion F a) :~: On) as H7. { apply Recursion2.IsFunctionOn. }
  split.
  - split.
    + apply Recursion2.IsFunctionOn.
    + split.
      * apply COC.EquivCompat with On.
          { apply Equiv.Sym. assumption. }
          { apply COC.OnIsOrdinal. }
      * admit.
  - intros b c H8 H9 H10. admit.
Admitted.
