Require Import ZF.Axiom.Continuum.
Require Import ZF.Class.Cardinal.Aleph.
Require Import ZF.Class.Cardinal.InfiniteCard.
Require Import ZF.Set.Cardinal.Equip.
Require Import ZF.Set.Cardinal.Finite.
Require Import ZF.Set.Cardinal.Number.
Require Import ZF.Set.Cardinal.Regular.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Ordinal.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Power.
Require Import ZF.Set.Relation.EvalOfClass.

Require Import ZF.Notation.Eval.


(* The set a is a weakly inaccessible cardinal.                                 *)
Definition WeaklyInaccessible (a:U) : Prop :=
  Regular a /\ exists b, Limit b /\ a = Aleph!b.

(* The set a is an inaccessible cardinal.                                       *)
Definition Inaccessible (a:U) : Prop :=
  WeaklyInaccessible a /\ forall x, card x :< a -> card :P(x) :< a.

(* A regular Aleph at a limit index is weakly inaccessible.                     *)
Proposition Charac : forall (a:U), Limit a ->
  Regular (Aleph!a) -> WeaklyInaccessible (Aleph!a).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1 H2. split. 1: assumption. exists a. split; try assumption.
  reflexivity.
Qed.

(* Weak inaccessibility of Aleph(a) forces a to be a limit index.               *)
Proposition CharacRev : forall (a:U), Ordinal a ->
  WeaklyInaccessible (Aleph!a) -> Limit a /\ Regular (Aleph!a).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1 H2.
  assert (Regular (Aleph!a)) as H3. { apply H2. }
  destruct H2 as [_ [b [H4 H5]]].
  assert (Ordinal b) as H6. { apply H4. }
  assert (a = b) as H7. { apply Aleph.Injective; assumption. }
  split. 2: assumption. rewrite H7. assumption.
Qed.

(* At a limit index under GCH, powers below Aleph(a) stay below Aleph(a).       *)
Proposition PowerBelowLimit : forall (a x:U),
  GCH -> Limit a -> card x :< Aleph!a -> card :P(x) :< Aleph!a.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a x GCH H2 H3.
  assert (Ordinal a) as G1. { apply H2. }
  assert (Ordinal (Aleph!a)) as G2. { apply Aleph.IsOrdinal. assumption. }
  assert (Ordinal (card x)) as G3. { apply Number.IsOrdinal. }
  assert (Cardinal (card x)) as G4. { exists x. reflexivity. }
  assert (card x :< :N \/ :N :<=: card x) as [H4|H4]. {
    apply Ordinal.ElemOrIncl; try assumption. apply Omega.IsOrdinal. }
  - (* Finite cardinals power to finite cardinals, hence stay below Aleph(a).   *)
    assert (card :P(x) :< :N) as H5. { apply Finite.CardPower. assumption. }
    assert (Ordinal (card :P(x))) as H6. { apply Number.IsOrdinal. }
    assert (:N :<=: Aleph!a) as H7. {
      rewrite <- Aleph.WhenZero.
      assert (Ordinal :0:) as H8. { apply Ordinal.Zero. }
      assert (:0: :<=: a) as H9. { apply Empty.IsIncl. }
      apply Aleph.InclCompat; assumption. }
    apply Ordinal.ElemInclTran with :N; try assumption. apply Omega.IsOrdinal.
  - (* Infinite cardinals below Aleph(a) are earlier Aleph values.              *)
    assert (InfiniteCard (card x)) as H5. {
      apply InfiniteCard.WhenIncl; assumption. }
    assert (exists b, Ordinal b /\ Aleph!b = card x) as H6. {
      apply Aleph.HasIndex. assumption. }
    destruct H6 as [b [H6 H7]].
    assert (Aleph!b :< Aleph!a) as H8. { rewrite H7. assumption. }
    assert (b :< a) as H9. { apply Aleph.ElemCompatRev; assumption. }
    assert (succ b :< a) as H10. { apply Limit.HasSucc; assumption. }
    assert (Ordinal (succ b)) as H11. { apply Succ.IsOrdinal. assumption. }
    assert (card :P(Aleph!b) = Aleph!(succ b)) as H12. { apply GCH. assumption. }
    assert (card x <> :0:) as H13. {
      apply InfiniteCard.IsNotZero. assumption. }
    assert (x :~: Aleph!b) as H14. {
      rewrite H7. apply Number.IsEquipNotZero. assumption. }
    assert (:P(x) :~: :P(Aleph!b)) as H15. {
      apply Equip.PowerCompat. assumption. }
    assert (card :P(x) = Aleph!(succ b)) as H16. {
      assert (card :P(x) = card :P(Aleph!b)) as H16. {
        apply Number.WhenEquip. assumption. }
      rewrite H16. assumption. }
    rewrite H16. apply Aleph.ElemCompat; assumption.
Qed.

(* Under GCH, weak inaccessibility and inaccessibility coincide.                *)
Proposition WhenGCH : forall (a:U),
  GCH -> (WeaklyInaccessible a <-> Inaccessible a).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a GCH. split; intros H1.
  - (* A weakly inaccessible cardinal is closed under powers by the limit case. *)
    assert (forall x, card x :< a -> card :P(x) :< a) as H2. {
      intros x H2.
      destruct H1 as [H3 [b [H4 H5]]].
      rewrite H5 in H2. rewrite H5.
      apply PowerBelowLimit; assumption. }
    split; assumption.
  - (* Inaccessibility already contains weak inaccessibility.                   *)
    apply H1.
Qed.

