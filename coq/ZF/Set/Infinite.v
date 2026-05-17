Require Import ZF.Axiom.Choice.
Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Finite.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Module CEM := ZF.Class.Empty.
Module SCC := ZF.Set.Cardinal.Core.
Module SCE := ZF.Set.Cardinal.Equiv.
Module SOC := ZF.Set.Ordinal.Core.
Module SOI := ZF.Set.Ordinal.InfOfClass.

(* A set is infinite if and only if it is not finite.                           *)
Definition Infinite (a:U) : Prop := ~ Finite a.

(* Infiniteness is preserved under equipotence.                                 *)
Proposition EquivCompat : forall (a b:U),
  a :~: b -> Infinite a -> Infinite b.
Proof.
  (* Proof by Claude.                                                           *)
  (* Infinite a means not Finite a. If b were finite, a ~ b would give          *)
  (* Finite a via Finite.EquivCompat, contradicting Infinite a.                 *)
  intros a b H1 H2 H3. apply H2.
  apply Finite.EquivCompat with b. 2: assumption.
  apply SCE.Sym. assumption.
Qed.

Proposition CardNotFiniteGen : forall (a:U), Infinite a ->
  (exists b, Ordinal b /\ a :~: b) -> :N :<=: card a.
Proof.
  intros a H1 H2.
  assert (Ordinal (card a)) as G1. { apply SCC.IsOrdinal. }
  assert (Ordinal :N) as G2. { apply Omega.IsOrdinal. }
  assert (card a :< :N \/ :N :<=: card a) as H3. {
    apply SOC.ElemOrIncl; assumption. }
  destruct H3 as [H3|H3]. 2: assumption. exfalso.
  apply H1. exists (card a). split. 1: assumption.
  apply SCC.IsEquivGen. assumption.
Qed.

Proposition CardNotFinite : forall (a:U), Choice ->
  Infinite a <-> :N :<=: card a.
Proof.
  intros a AC.
  assert (exists b, Ordinal b /\ a :~: b) as H1. {
    apply SCE.HasOrdinal. assumption. }
  split; intros H2.
  - apply CardNotFiniteGen; assumption.
  - intros [n [H3 H4]].
    assert (card a = card n) as H5. { apply SCC.WhenEquiv. assumption. }
    assert (card n = n) as H6. { apply SCC.WhenNat. assumption. }
    assert (n :< n) as H7. { rewrite H5, H6 in H2. apply H2. assumption. }
    revert H7. apply Foundation.NoLoop1.
Qed.

(* Adding an element to an infinite set does not change its cardinal.           *)
Proposition AddElem : forall (a b:U), Infinite a ->
  card a = card (a :\/: :{b}:).
Proof.
  (* Proof by Claude. *)
  intros a b H1.
  (* Split by whether b is already in a.                                         *)
  assert (a :\/: :{b}: = a \/ a :\/: :{b}: :~: succ a) as [H2|H2]. {
    apply SCE.AddElem. }
  (* If b is already in a then a ∪ {b} = a and the cardinal is unchanged.       *)
  - rewrite H2. reflexivity.
  (* Otherwise a ∪ {b} is equipotent to succ(a), so card(a ∪ {b}) = card(succ a)*)
  (* and it suffices to show card a = card(succ a).                              *)
  - assert (card (a :\/: :{b}:) = card (succ a)) as H3. {
      apply SCC.WhenEquiv. assumption. }
    rewrite H3.
    (* Split by whether a has an equivalent ordinal.                             *)
    assert (WithOrdinal a \/ ~ WithOrdinal a) as [H4|H4]. {
      apply LawExcludedMiddle. }
    + (* a has an equivalent ordinal: a ≅ card a, and a is infinite so N ≤ card a.*)
      assert (a :~: card a) as H5. { apply SCC.IsEquivGen. assumption. }
      assert (:N :<=: card a) as H6. { apply CardNotFiniteGen; assumption. }
      assert (Ordinal (card a)) as H7. { apply SCC.IsOrdinal. }
      (* card a is an ordinal with N ≤ card a, so card a ≅ succ(card a).         *)
      assert (card a :~: succ (card a)) as H8. { apply SCE.Succ; assumption. }
      (* SuccCompat gives succ a ≅ succ(card a), hence card(succ a) = card(succ(card a)).*)
      assert (succ a :~: succ (card a)) as H9. {
        apply SCE.SuccCompat. assumption. }
      assert (card (succ a) = card (succ (card a))) as H10. {
        apply SCC.WhenEquiv. assumption. }
      (* card a = card(card a) = card(succ(card a)) = card(succ a).              *)
      assert (card (card a) = card (succ (card a))) as H11. {
        apply SCC.WhenEquiv. assumption. }
      rewrite <- (SCC.Idem a), H11, <- H10. reflexivity.
    + (* a has no equivalent ordinal. If succ a had an equivalent ordinal c with  *)
      (* bijection f, restricting f to a gives a ≅ f[a] ≅ some ordinal, which   *)
      (* contradicts the assumption. So succ a also has no equivalent ordinal,    *)
      (* and both cardinals equal 0.                                              *)
      assert (~ WithOrdinal (succ a)) as H5. {
        intros [c [H5 H6]]. apply H4.
        destruct H6 as [f H6].
        assert (Bij (f :|: a) a (f:[a]:)) as K1. {
          apply (Bij.Restrict f (succ a) c a).
          1: assumption. apply Succ.IsIncl. }
        assert (a :~: f:[a]:) as K2. { exists (f :|: a). assumption. }
        assert (f:[a]: :<=: c) as K3. {
          intros y Ky.
          apply (Bij.ImageCharac f (succ a) c a) in Ky. 2: assumption.
          destruct Ky as [x [Kx [Kxa Ky]]]. rewrite <- Ky.
          apply (Bij.IsInRange f (succ a) c); assumption. }
        assert (exists m, Ordinal m /\ m :<=: c /\ f:[a]: :~: m) as K4. {
          apply SCE.OrdinalSubset; assumption. }
        destruct K4 as [m [K4 [_ K5]]].
        exists m. split. 1: assumption.
        apply SCE.Tran with f:[a]:; assumption. }
      rewrite (SCC.WhenNoOrdinal a H4).
      rewrite (SCC.WhenNoOrdinal (succ a) H5).
      reflexivity.
Qed.
