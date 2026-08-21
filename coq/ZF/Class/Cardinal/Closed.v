Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Closed.
Require Import ZF.Class.Relation.EvalAsClass.
Require Import ZF.Class.Relation.Fun.From.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Cardinal.Number.
Require Import ZF.Set.Cardinal.WithChoice.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Union2.
Require Import ZF.Set.UnionGenOfClass.


(* A unary image in the closure construction is bounded by its source.          *)
Proposition UnaryImageIncl : forall (R:Class) (i x:U), Choice ->
  Functional R$i -> card (unaryImage R i x) :<=: card x.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros R i x AC H1.
  apply WithChoice.ImageIncl; assumption.
Qed.

(* A binary image in the closure construction is bounded by an infinite source. *)
Proposition BinaryImageIncl : forall (S:Class) (i x:U), Choice ->
  :N :<=: card x -> Functional S$i -> card (binaryImage S i x) :<=: card x.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros S i x AC H1 H2.
  (* The image of x^2 is bounded by x^2.                                        *)
  assert (card (binaryImage S i x) :<=: card (x :x: x)) as H3. {
    apply WithChoice.ImageIncl; assumption. }
  (* Since x is infinite, its square has the same cardinal as x.                *)
  assert (card (x :x: x) = card x) as H4. { apply Number.Square. assumption. }
  rewrite H4 in H3. assumption.
Qed.

(* The unary part of one stage is bounded by an infinite source.                *)
Proposition UnaryUnionIncl : forall (R:Class) (p x:U), Choice -> p :< :N ->
  :N :<=: card x                        ->
  (forall i, i :< p -> Functional R$i)  ->
  card (unaryUnion R p x) :<=: card x.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros R p x AC H1 H2 H3.
  apply WithChoice.UnionGenFinite; try assumption.
  intros i H4.
  rewrite Class.Relation.Fun.From.Eval.
  apply UnaryImageIncl; try assumption.
  apply H3. assumption.
Qed.

(* The binary part of one stage is bounded by an infinite source.               *)
Proposition BinaryUnionIncl : forall (S:Class) (q x:U), Choice -> q :< :N ->
  :N :<=: card x                        ->
  (forall i, i :< q -> Functional S$i)  ->
  card (binaryUnion S q x) :<=: card x.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros S q x AC H1 H2 H3.
  apply WithChoice.UnionGenFinite; try assumption.
  intros i H4.
  rewrite Class.Relation.Fun.From.Eval.
  apply BinaryImageIncl; try assumption.
  apply H3. assumption.
Qed.

(* Every finite stage of the closure sequence has the original cardinal.        *)
Proposition SeqCard : forall (R S:Class) (p q a n:U), Choice ->
  :N :<=: card a                         ->
  p :< :N                                ->
  q :< :N                                ->
  n :< :N                                ->
  (forall i, i :< p -> Functional R$i)   ->
  (forall i, i :< q -> Functional S$i)   ->
  card (seq R S p q a)!n = card a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros R S p q a n AC H1 H2 H3 H4 H5 H6.
  remember (fun n => card (seq R S p q a)!n = card a) as A eqn:HA.
  assert (forall n, n :< :N -> A n) as H7. {
    apply Omega.Induction.
    - rewrite HA. rewrite Closed.WhenZero. reflexivity.
    - intros m H7 IH. rewrite HA in IH. rewrite HA.
      rewrite Closed.WhenSucc. 2: assumption. unfold step. rewrite <- Union2.Assoc.
      remember (seq R S p q a)!m as x eqn:H8.
      (* The induction hypothesis makes the current stage infinite.             *)
      assert (:N :<=: card x) as H9. { rewrite IH. assumption. }
      (* The unary part is absorbed by the current stage.                       *)
      assert (card (unaryUnion R p x) :<=: card x) as H10. {
        apply UnaryUnionIncl; assumption. }
      assert (card (x :\/: unaryUnion R p x) = card x) as H11. {
        apply WithChoice.UnionL; assumption. }
      (* The binary part is absorbed after the unary part has been added.       *)
      assert (:N :<=: card (x :\/: unaryUnion R p x)) as H12. {
        rewrite H11. assumption. }
      assert (card (binaryUnion S q x) :<=: card x) as H13. {
        apply BinaryUnionIncl; assumption. }
      assert (card (binaryUnion S q x) :<=: card (x :\/: unaryUnion R p x)) as H14. {
        rewrite H11. assumption. }
      assert (card ((x :\/: unaryUnion R p x) :\/: binaryUnion S q x) =
        card (x :\/: unaryUnion R p x)) as H15. {
        apply WithChoice.UnionL; assumption. }
      rewrite H15. rewrite H11. assumption. }
  assert (A n) as H8. { apply H7. assumption. }
  rewrite HA in H8. assumption.
Qed.

(* The closure hull is bounded by the original infinite cardinal.               *)
Proposition HullCardIncl : forall (R S:Class) (p q a:U), Choice ->
  :N :<=: card a                         ->
  p :< :N                                ->
  q :< :N                                ->
  (forall i, i :< p -> Functional R$i)   ->
  (forall i, i :< q -> Functional S$i)   ->
  card (hull R S p q a) :<=: card a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros R S p q a AC H1 H2 H3 H4 H5.
  (* The omega-union is bounded by N times the original set.                    *)
  assert (card (:\/:_{:N} (seq R S p q a)) :<=: card (:N :x: a)) as H6. {
    apply WithChoice.UnionGenProdSet. 1: assumption.
    intros n H6. assert (card (seq R S p q a)!n = card a) as H7. {
      apply SeqCard; assumption. }
    rewrite H7. apply Incl.Refl. }
  (* Since a is infinite, N x a is bounded by a x a.                            *)
  assert (card (:N :x: a) :<=: card (a :x: a)) as H7. {
    apply WithChoice.InclCompatProd. 1: assumption.
    - rewrite Number.WhenOmega. assumption.
    - apply Incl.Refl. }
  (* The square of an infinite set has the same cardinal as the set.            *)
  assert (card (a :x: a) = card a) as H8. { apply Number.Square. assumption. }
  rewrite H8 in H7. apply Incl.Tran with (card (:N :x: a)); assumption.
Qed.
