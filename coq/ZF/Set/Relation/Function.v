Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Relation.


(* A set is a function iff it is a relation and it is functional.               *)
Definition Function (f:U) : Prop := Relation f /\ Functional f.

(* Two functions with the same domain which coincide pointwise are equal.       *)
Proposition EqualCharac : forall (f g:U),
  Function f                                ->
  Function g                                ->
  domain f = domain g                       -> 
  (forall x, x :< domain f -> f!x = g!x)  ->
  f = g.
Proof.
  intros f g [H1 H2] [H3 H4] H5 H6. apply DoubleInclusion. split; intros x H7.
  - specialize (H1 x H7). destruct H1 as [y [z H1]]. subst.
    assert (y :< domain f) as H8. { apply Domain.Charac. exists z. assumption. }
    assert (f!y = z) as H9. { apply Eval.Charac; assumption. }
    assert (g!y = z) as H10. { rewrite <- H9. symmetry. apply H6. assumption. }
    rewrite <- H10. apply Eval.Satisfies. 1: assumption.
    rewrite <- H5. assumption. 
  - specialize (H3 x H7). destruct H3 as [y [z H3]]. subst.
    assert (y :< domain g) as H8. { apply Domain.Charac. exists z. assumption. }
    assert (g!y = z) as H9. { apply Eval.Charac; assumption. }
    assert (f!y = z) as H10. { rewrite <- H9. apply H6. rewrite H5. assumption. }
    rewrite <- H10. apply Eval.Satisfies. 1: assumption.
    rewrite H5. assumption.
Qed.



 
