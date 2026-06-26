Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.AntiSymmetric.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.Transport.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Eval.

Module COA := ZF.Class.Order.AntiSymmetric.

(* Predicate expressing the fact that r is an anti-symmetric set on a.          *)
Definition AntiSymmetric (r a:U) : Prop := forall (x y:U), x :< a -> y :< a ->
  :(x,y): :< r -> :(y,x): :< r -> x = y.

(* If the sets form an anti-symmetric pair, then so do the classes.             *)
Proposition ToClass : forall (r a:U),
  AntiSymmetric r a -> COA.AntiSymmetric (toClass r) (toClass a).
Proof.
  intros r a H1. assumption.
Qed.

(* If the classes form an anti-symmetric pair, then so do the sets.             *)
Proposition FromClass : forall (r a:U),
  COA.AntiSymmetric (toClass r) (toClass a) -> AntiSymmetric r a.
Proof.
  intros r a H1. assumption.
Qed.

(* Anti-symmetry on a restricts to anti-symmetry on any subset b.               *)
Proposition InclCompat : forall (r a b:U),
  b :<=: a -> AntiSymmetric r a -> AntiSymmetric r b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* Elements of b are elements of a, so the larger-domain property applies.    *)
  intros r a b H1 H2 x y H3 H4 H5 H6.
  apply H2; try assumption; apply H1; assumption.
Qed.

(* Anti-symmetry is preserved and reflected by order isomorphisms.              *)
Proposition IsomCompat : forall (f r s a b:U),
  Isom f r s a b -> AntiSymmetric r a <-> AntiSymmetric s b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* It is sufficient to prove one implication.                                 *)
  assert (forall (f r s a b:U),
    Isom f r s a b -> AntiSymmetric r a -> AntiSymmetric s b) as L. {
    intros f r s a b H1 H2 y1 y2 H3 H4 H5 H6.
    assert (H7 := H1). destruct H7 as [H7 H8].
    remember (eval (f^:-1:) y1) as x1 eqn:H9.
    remember (eval (f^:-1:) y2) as x2 eqn:H10.
    assert (x1 :< a) as H11. { rewrite H9.
      apply Bij.ConverseEvalIsInDomain with b; assumption. }
    assert (x2 :< a) as H12. { rewrite H10.
      apply Bij.ConverseEvalIsInDomain with b; assumption. }
    assert (y1 = f!x1) as H13. { rewrite H9. symmetry.
      apply Bij.EvalOfConverseEval with a b; assumption. }
    assert (y2 = f!x2) as H14. { rewrite H10. symmetry.
      apply Bij.EvalOfConverseEval with a b; assumption. }
    assert (:(x1,x2): :< r) as H15. {
      apply H8; try assumption. rewrite <- H13, <- H14. assumption. }
    assert (:(x2,x1): :< r) as H16. {
      apply H8; try assumption. rewrite <- H14, <- H13. assumption. }
    assert (x1 = x2) as H17. { apply H2; assumption. }
    rewrite H13, H14, H17. reflexivity.
  }
  (* The converse direction follows from applying the same implication to f^-1. *)
  intros f r s a b H1. split.
  - apply L with f. assumption.
  - apply L with f^:-1:, Isom.Converse. assumption.
Qed.

(* Anti-symmetry is preserved under transport by a bijection.                   *)
Proposition Transport : forall (f r s a b:U),
  s = transport f r a  ->
  Bij f a b            ->
  AntiSymmetric r a    ->
  AntiSymmetric s b.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros f r s a b H1 H2 H3 y1 y2 H4 H5 H6 H7.
  apply (Bij.RangeCharac f a b) in H4. 2: assumption.
  apply (Bij.RangeCharac f a b) in H5. 2: assumption.
  destruct H4 as [x1 [H4 H8]]. destruct H5 as [x2 [H5 H9]].
  rewrite <- H8, <- H9 in H6. rewrite H1 in H6.
  rewrite <- H9, <- H8 in H7. rewrite H1 in H7.
  apply (Transport.Charac2f f r a b) in H6. 2-4: assumption.
  apply (Transport.Charac2f f r a b) in H7. 2-4: assumption.
  assert (x1 = x2) as H10. { apply H3; assumption. }
  rewrite <- H8, <- H9. rewrite H10. reflexivity.
Qed.
