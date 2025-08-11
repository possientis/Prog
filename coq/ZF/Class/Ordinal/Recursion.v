Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Induction.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Restrict.

(* Transfinite recursion class associated with a class F.                       *)
Definition Recursion (F:Class) : Class := fun x => exists f, exists b,
  x :< f                                  /\
  On b                                    /\
  FunctionOn f b                          /\
  (forall a, a :< b -> f!a = F!(f:|:a)).

Lemma Coincide : forall (F:Class) (f g a b:U),
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
    - intros c H9 H10. rewrite H8. split. 1: assumption. intros H11.
      assert (f:|:c = g:|:c) as H12. {
        assert (c :<=: a) as H12. {
          apply ZF.Set.Ordinal.Core.LessIsElem; assumption. }
        apply FunctionOn.RestrictEqual with a b; try assumption.
        + apply Incl.Tran with a; assumption.
        + intros x H13.
          assert (A x) as H14. { apply H10. assumption. }
          rewrite H8 in H14. destruct H14 as [H14 H15].
          apply H15, H12. assumption. }
          rewrite H6, H7, H12. 1: reflexivity. 2: assumption.
          apply H3. assumption. }
  intros x H10.
  assert (On x) as H11. { apply ZF.Set.Ordinal.Core.IsOrdinal with a; assumption. }
  assert (A x) as H12. { apply H9. assumption. }
  rewrite H8 in H12. destruct H12 as [_ H12]. apply H12. assumption.
Qed.

(* The transfinite recursion class associated with F is a relation.             *)
Proposition IsRelation : forall (F:Class), Relation (Recursion F).
Proof.
  intros F x H1. destruct H1 as [f [b [H1 [_ [[[H2 _] _] _]]]]].
  specialize (H2 x H1). assumption.
Qed.

(* The transfinite recursion class associated with F is a function.            *)
Proposition IsFunction : forall (F:Class), Function (Recursion F).
Proof.
  intros F. split. 1: apply IsRelation. intros x y z H1 H2.
  destruct H1 as [f [a [H1 [H3 [H4 H5]]]]].
  destruct H2 as [g [b [H2 [H6 [H7 H8]]]]].
  assert (a :<=: b \/ b :<=: a) as H9. {
    apply ZF.Set.Ordinal.Core.InclOrIncl; assumption. }
  assert (x :< a) as H10. {
    destruct H4 as [_ H4]. rewrite <- H4.
    apply Domain.Charac. exists y. assumption. }
  assert (x :< b) as H11. {
    destruct H7 as [_ H7]. rewrite <- H7.
    apply Domain.Charac. exists z. assumption. }
  assert (f!x = y) as H12. { apply (FunctionOn.EvalCharac f a); assumption. }
  assert (g!x = z) as H13. { apply (FunctionOn.EvalCharac g b); assumption. }
Admitted.
