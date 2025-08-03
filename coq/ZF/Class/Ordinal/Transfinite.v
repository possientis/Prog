Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Less.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Restrict.


(* Principle of transfinite induction.                                          *)
Proposition Induction : forall (A:Class),
  A :<=: On                                   ->
  (forall a, On a -> toClass a :<=: A -> A a) ->
  A :~: On.
Proof.
  intros A H1 H2. apply DoubleNegation. intros H3.
  assert (On :\: A :<>: :0:) as H4. { apply Diff.WhenLess. split; assumption. }
  assert (exists a, (On :\: A) a /\ (On :\: A) :/\: toClass a :~: :0:) as H5. {
    apply HasEMinimal with On. 3: assumption.
    - apply OnIsOrdinal.
    - apply Class.Inter2.IsInclL. }
  destruct H5 as [a [[H5 H6] H7]]. assert (toClass a :<: On) as H8. {
    apply LessIsElem; try assumption. apply OnIsOrdinal. }
  assert (toClass a :<=: A) as H9. {
    intros x H10. apply DoubleNegation. intros H11.
    apply Class.Empty.Charac with x, H7. split. 2: assumption. split. 2: assumption.
    apply IsOrdinal with (toClass a); assumption. }
  apply H6, H2; assumption.
Qed.

Proposition Coincide : forall (F:Class) (f g a b:U),
  On a                                  ->
  On b                                  ->
  a :<=: b                              ->
  FunctionOn f a                        ->
  FunctionOn g b                        ->
  (forall x, x :< a -> f!x = F!(f:|:x)) ->
  (forall x, x :< b -> g!x = F!(g:|:x)) ->
  (forall x, x :< a -> f!x = g!x).
Proof.
  intros F f g a b H1 H2 H3 H4 H5 H6 H7.
  remember (fun x => On x /\ (x :< a -> f!x = g!x)) as A eqn:H8.
  assert (A :~: On) as H9. {
    apply Induction.
    - intros x H9. rewrite H8 in H9. apply H9.
    - intros c H9 H10. rewrite H8. split. 1: assumption. intros H11. Admitted.
(*
  intros x H10.
  assert (On x) as H11. { apply IsOrdinal with (toClass a); assumption. }
  assert (A x) as H12. { apply H9. assumption. }
  rewrite H8 in H12. destruct H12 as [_ H12]. apply H12. assumption.
*)

