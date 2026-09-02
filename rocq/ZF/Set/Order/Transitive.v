Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Transitive.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.Transport.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Eval.

Module COT := ZF.Class.Order.Transitive.

(* Predicate expressing the fact that r is a transitive set (as relation) on a. *)
Definition Transitive (r a:U) : Prop := forall (x y z:U),
  x :< a        ->
  y :< a        ->
  z :< a        ->
  :(x,y): :< r  ->
  :(y,z): :< r  ->
  :(x,z): :< r.

(* If the sets form a transitive pair, then so do the classes.                  *)
Proposition ToClass : forall (r a:U),
  Transitive r a -> COT.Transitive (toClass r) (toClass a).
Proof.
  intros r a H1. assumption.
Qed.

(* If the classes form a transitive pair, then so do the sets.                  *)
Proposition FromClass : forall (r a:U),
  COT.Transitive (toClass r) (toClass a) -> Transitive r a.
Proof.
  intros r a H1. assumption.
Qed.

(* Transitivity on a restricts to transitivity on any subset b.                 *)
Proposition InclCompat : forall (r a b:U),
  b :<=: a -> Transitive r a -> Transitive r b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* Elements of b are elements of a, so the larger-domain property applies.    *)
  intros r a b H1 H2 x y z H3 H4 H5 H6 H7.
  apply H2 with y; try assumption; apply H1; assumption.
Qed.

(* Transitivity is preserved and reflected by order isomorphisms.               *)
Proposition IsomCompat : forall (f r s a b:U),
  Isom f r s a b -> Transitive r a <-> Transitive s b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* It is sufficient to prove one implication.                                 *)
  assert (forall (f r s a b:U),
    Isom f r s a b -> Transitive r a -> Transitive s b) as L. {
    intros f r s a b H1 H2 z1 z2 z3 H3 H4 H5 H6 H7.
    assert (H8 := H1). destruct H8 as [H8 H9].
    remember (f^:-1:!z1) as y1 eqn:H10.
    remember (f^:-1:!z2) as y2 eqn:H11.
    remember (f^:-1:!z3) as y3 eqn:H12.
    assert (y1 :< a) as H13. { rewrite H10.
      apply Bij.ConverseEvalIsInDomain with b; assumption. }
    assert (y2 :< a) as H14. { rewrite H11.
      apply Bij.ConverseEvalIsInDomain with b; assumption. }
    assert (y3 :< a) as H15. { rewrite H12.
      apply Bij.ConverseEvalIsInDomain with b; assumption. }
    assert (z1 = f!y1) as H16. { rewrite H10. symmetry.
      apply Bij.EvalOfConverseEval with a b; assumption. }
    assert (z2 = f!y2) as H17. { rewrite H11. symmetry.
      apply Bij.EvalOfConverseEval with a b; assumption. }
    assert (z3 = f!y3) as H18. { rewrite H12. symmetry.
      apply Bij.EvalOfConverseEval with a b; assumption. }
    assert (:(y1,y2): :< r) as H19. {
      apply H9; try assumption. rewrite <- H16, <- H17. assumption. }
    assert (:(y2,y3): :< r) as H20. {
      apply H9; try assumption. rewrite <- H17, <- H18. assumption. }
    rewrite H16, H18. apply H9; try assumption.
    apply H2 with y2; assumption.
  }
  (* The converse direction follows from applying the same implication to f^-1. *)
  intros f r s a b H1. split.
  - apply L with f. assumption.
  - apply L with f^:-1:, Isom.Converse. assumption.
Qed.

(* Transitivity is preserved under transport by a bijection.                    *)
Proposition Transport : forall (f r s a b:U),
  s = transport f r a ->
  Bij f a b           ->
  Transitive r a      ->
  Transitive s b.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros f r s a b H1 H2 H3 x y z H4 H5 H6 H7 H8.
  apply (Bij.RangeCharac f a b) in H4. 2: assumption.
  apply (Bij.RangeCharac f a b) in H5. 2: assumption.
  apply (Bij.RangeCharac f a b) in H6. 2: assumption.
  destruct H4 as [x1 [H4 H9]]. destruct H5 as [x2 [H5 H10]].
  destruct H6 as [x3 [H6 H11]].
  rewrite <- H9, <- H10 in H7. rewrite H1 in H7.
  rewrite <- H10, <- H11 in H8. rewrite H1 in H8.
  apply (Transport.Charac2f f r a b) in H7. 2-4: assumption.
  apply (Transport.Charac2f f r a b) in H8. 2-4: assumption.
  rewrite <- H9, <- H11. rewrite H1.
  apply (Transport.Charac2f f r a b). 1-3: assumption.
  apply H3 with x2; assumption.
Qed.
