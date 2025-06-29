Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that R is a total class on A.                  *)
Definition Total (R A:Class) : Prop := forall (x y:U), A x -> A y ->
  x = y \/ R :(x,y): \/ R :(y,x):.

Proposition TotalIncl : forall (R A B:Class),
  Total R A -> B :<=: A -> Total R B.
Proof.
  intros R A B H1 H2 x y H3 H4. apply H1; apply H2; assumption.
Qed.

Proposition TotalIsom : forall (F R S A B:Class),
  Isom F R S A B -> Total R A <-> Total S B.
Proof.
  (* It is sufficient to prove -> *)
  assert (forall (F R S A B:Class),
    Isom F R S A B -> Total R A -> Total S B) as L. {
    intros F R S A B H1 H2 y1 y2 H3 H4. assert (H5 := H1). destruct H5 as [H5 H6].
    remember (F^:-1:!y1) as x1 eqn:H7. remember (F^:-1:!y2) as x2 eqn:H8.
    assert (A x1) as H9.  { rewrite H7.
      apply Bij.ConverseEvalIsInDomain with B; assumption. }
    assert (A x2) as H10. { rewrite H8.
      apply Bij.ConverseEvalIsInDomain with B; assumption. }
    assert (y1 = F!x1) as H11. { rewrite H7. symmetry.
      apply Bij.EvalOfConverseEval with A B; assumption. }
    assert (y2 = F!x2) as H12. { rewrite H8. symmetry.
      apply Bij.EvalOfConverseEval with A B; assumption. }
    specialize (H2 x1 x2 H9 H10).
    destruct H2 as [H2|[H2|H2]].
    - left. rewrite H11, H12, H2. reflexivity.
    - right. left.  rewrite H11, H12. specialize (H6 x1 x2 H9 H10). apply H6. assumption.
    - right. right. rewrite H11, H12. specialize (H6 x2 x1 H10 H9). apply H6. assumption.
  }
  (* The proof of the equivalence follows. *)
  intros F R S A B H1. split.
  - apply L with F. assumption.
  - apply L with F^:-1:, Isom.Converse. assumption.
Qed.
