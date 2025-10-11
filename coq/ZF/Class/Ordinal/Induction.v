Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Less.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Union.

Module COC := ZF.Class.Ordinal.Core.

(* Principle of transfinite induction.                                          *)
Proposition Induction : forall (A:Class),
  A :<=: On                                   ->
  (forall a, On a -> toClass a :<=: A -> A a) ->
  A :~: On.
Proof.
  intros A H1 H2. apply DoubleNegation. intros H3.
  assert (On :\: A :<>: :0:) as H4. { apply Diff.WhenLess. split; assumption. }
  assert (exists a, (On :\: A) a /\ (On :\: A) :/\: toClass a :~: :0:) as H5. {
    apply COC.HasMinimal with On. 3: assumption.
    - apply OnIsOrdinal.
    - apply Class.Inter2.IsInclL. }
  destruct H5 as [a [[H5 H6] H7]]. assert (toClass a :<: On) as H8. {
    apply Class.Ordinal.Core.LessIsElem; try assumption. apply OnIsOrdinal. }
  assert (toClass a :<=: A) as H9. {
    intros x H10. apply DoubleNegation. intros H11.
    apply Class.Empty.Charac with x, H7. split. 2: assumption. split. 2: assumption.
    apply Class.Ordinal.Core.IsOrdinal with (toClass a); assumption. }
  apply H6, H2; assumption.
Qed.

Proposition Induction' : forall (A:Class),
  (forall a, On a -> (forall x, x :< a -> A x) -> A a) ->
   forall a, On a -> A a.
Proof.
  intros A H1.
  remember (fun x => On x /\ A x) as B eqn:H2.
  assert (B :~: On) as H3. {
    apply Induction.
    - intros x H3. rewrite H2 in H3. apply H3.
    - intros a H3 H4. rewrite H2. split. 1: assumption.
      apply H1. 1: assumption. intros x H5.
      assert (B x) as H6. { apply H4. assumption. }
      rewrite H2 in H6. apply H6. }
      intros a H4. apply H3 in H4. rewrite H2 in H4. apply H4.
Qed.
