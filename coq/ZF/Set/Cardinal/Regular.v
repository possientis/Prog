Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Cardinal.Aleph.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Cardinal.InfiniteCard.
Require Import ZF.Set.Cardinal.Number.
Require Import ZF.Set.Cardinal.WithChoice.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Cofinal.
Require Import ZF.Set.Ordinal.Character.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Monotone.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Ordinal.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Union.
Require Import ZF.Set.UnionGen.

Require Import ZF.Notation.Eval.


Module CRL := ZF.Class.Relation.Functional.

(* The set a is a regular cardinal.                                             *)
Definition Regular (a:U) : Prop := InfiniteCard a /\ charac a = a.

(* The zeroth Aleph cardinal is regular.                                        *)
Proposition WhenZero : Regular (Aleph!:0:).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  split.
  - apply Aleph.IsInfiniteCard. apply Ordinal.Zero.
  - rewrite Aleph.WhenZero. apply Character.WhenOmega.
Qed.

(* The character of the zeroth Aleph is the zeroth Aleph.                       *)
Proposition WhenZeroCharac : charac Aleph!:0: = Aleph!:0:.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  (* Regularity of the zeroth Aleph includes precisely this character equality. *)
  assert (Regular (Aleph!:0:)) as H1. { apply WhenZero. }
  apply H1.
Qed.

(* The Aleph value at a successor ordinal is a regular cardinal.                *)
Proposition WhenSucc : forall (a:U), Choice ->
  Ordinal a -> Regular (Aleph! (succ a)).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a AC H1.
  assert (Ordinal (succ a)) as G1. { apply Succ.IsOrdinal. assumption. }
  assert (InfiniteCard Aleph!(succ a)) as H2. {
    apply Aleph.IsInfiniteCard. assumption. }
  split. 1: assumption.
  assert (Ordinal Aleph!(succ a)) as G2. { apply Aleph.IsOrdinal. assumption. }
  assert (Cardinal Aleph!(succ a)) as G3. { apply Aleph.IsCardinal. assumption. }
  assert (Aleph!a :< Aleph!(succ a)) as G4. {
    apply Aleph.ElemCompat; try assumption. apply Succ.IsIn. }
  assert (charac Aleph!(succ a) :<=: Aleph!(succ a)) as H3. {
    apply Character.IsIncl. assumption. }
  assert (Aleph!(succ a) :<=: charac Aleph!(succ a)) as H4. {
    apply Ordinal.EqualOrElem in H3. 3: assumption. 2: apply Character.IsOrdinal.
    destruct H3 as [H3|H3].
    - rewrite H3. apply Incl.Refl.
    - exfalso.
      (* If the character were smaller, it is an earlier Aleph value.           *)
      assert (InfiniteCard (charac Aleph!(succ a))) as K1. {
        apply Character.IsInfiniteCard. assumption. }
      assert (exists b, Ordinal b /\ Aleph!b = charac Aleph!(succ a)) as K2. {
        apply Aleph.HasIndex. assumption. }
      destruct K2 as [b [K2 K3]].
      assert (Aleph!b :< Aleph!(succ a)) as K4. { rewrite K3. assumption. }
      assert (b :< succ a) as K5. { apply Aleph.ElemCompatRev; assumption. }
      assert (b :<=: a) as K6. { apply Succ.InclIsElem; assumption. }
      assert (Aleph!b :<=: Aleph!a) as K7. {
        apply Aleph.InclCompat; assumption. }
      assert (Limit Aleph!(succ a)) as K8. {
        apply InfiniteCard.IsLimit. assumption. }
      assert (Cofinal Aleph!(succ a) (Aleph!b)) as K9. {
        rewrite K3. apply Character.IsCofinal. assumption. }
      assert (exists f, Monotone f /\ Fun f (Aleph!b) (Aleph!(succ a)) /\
        Aleph!(succ a) = :\/:_{Aleph!b} f) as K10. {
        apply Cofinal.UnionGen; assumption. }
      destruct K10 as [f [_ [K10 K11]]].
      assert (Functional f) as K12. { apply K10. }
      assert (CRL.Functional (toClass f)) as K13. {
        apply Functional.ToClass. assumption. }
      (* Proposition 10.48 bounds the union by the product of index and bound.  *)
      assert (card :U((toClass f):[Aleph!b]:) :<=:
        card (Aleph!b :x: Aleph!a)) as K14. {
        apply WithChoice.UnionProdImage; try assumption.
        intros x K14.
        assert ((toClass f)!x :< Aleph!(succ a)) as K15. {
          apply Fun.IsInRange with (Aleph!b); assumption. }
        assert (card ((toClass f)!x) :<=: Aleph!a) as K16. {
          apply Aleph.CardBelowSucc; assumption. }
        assert (Aleph!a = card Aleph!a) as K17. {
          apply Number.WhenCardinal. apply Aleph.IsCardinal. assumption. }
        rewrite <- K17. assumption. }
      assert (f:[Aleph!b]: = (toClass f):[Aleph!b]:) as K15. {
        apply Image.ByClass. }
      assert (:\/:_{Aleph!b} f = :U(f:[Aleph!b]:)) as K16. {
        apply ZF.Set.UnionGen.WhenImage. apply K10. }
      rewrite <- K15 in K14. rewrite <- K16 in K14. rewrite <- K11 in K14.
      assert (Aleph!(succ a) = card Aleph!(succ a)) as K17. {
        apply Number.WhenCardinal. assumption. }
      rewrite <- K17 in K14.
      assert (card (Aleph!b :x: Aleph!a) :<=:
        card (Aleph!a :x: Aleph!a)) as K18. {
        apply WithChoice.InclCompatProdL. 1: assumption.
        apply WithChoice.InclCompat; assumption. }
      assert (card (Aleph!a :x: Aleph!a) = Aleph!a) as K19. {
        rewrite Number.SquareOrd.
        + symmetry. apply Number.WhenCardinal. apply Aleph.IsCardinal. assumption.
        + apply Aleph.IsOrdinal. assumption.
        + apply InfiniteCard.IsIncl. apply Aleph.IsInfiniteCard. assumption. }
      assert (Aleph!(succ a) :<=: Aleph!a) as K20. {
        apply Incl.Tran with (card (Aleph!b :x: Aleph!a)). 1: assumption.
        rewrite K19 in K18. assumption. }
      assert (Aleph!a :< Aleph!a) as K21. { apply K20. assumption. }
      apply Foundation.NoLoop1 with Aleph!a. assumption. }
  apply Incl.Double. split; assumption.
Qed.

(* The character of a successor-indexed Aleph is that Aleph.                    *)
Proposition WhenSuccCharac : forall (a:U), Choice ->
  Ordinal a -> charac Aleph!(succ a) = Aleph!(succ a).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a AC H1.
  (* Regularity of the successor Aleph includes the character equality.         *)
  assert (Regular (Aleph!(succ a))) as H2. { apply WhenSucc; assumption. }
  apply H2.
Qed.

