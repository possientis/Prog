Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Finite.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Module CEM := ZF.Class.Empty.
Module SCC := ZF.Set.Cardinal.Core.
Module SCE := ZF.Set.Cardinal.Equiv.
Module SOC := ZF.Set.Ordinal.Core.
Module SOI := ZF.Set.Ordinal.InfOfClass.

(* The class of infinite sets, those which are not finite.                      *)
Definition Infinite : Class := fun a => ~ Finite a.

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

(* Adding an element to an infinite set does not change its cardinal.           *)
Proposition AddElem : forall (a b:U), Infinite a ->
  card a = card (a :\/: :{b}:).
Proof.
  intros a b H1.
  assert (a :\/: :{b}: = a \/ a :\/: :{b}: :~: succ a) as H2. {
    apply SCE.AddElem. }
  destruct H2 as [H2|H2].
  - rewrite H2. reflexivity.
  - Admitted.

(*
    assert (card a = :0: \/ card a <> :0:) as [H3|H3]. {
      apply LawExcludedMiddle. }
      assert (card (a :\/: :{b}:) = :0:) as H4. {
        apply SOI.IsZero. intros x. split; intros H4. 2: contradiction.
        exfalso. destruct H4 as [[H4 H5] _].
        assert (succ a :~: x) as H6. {
          apply SCE.Tran with (a :\/: :{b}:).
          - apply SCE.Sym. assumption.
          - assumption. }
        destruct H6 as [f H6].
        assert (a :~: f:[a]:) as H7. {
          exists (f :|: a). apply Bij.Restrict with (succ a) x.
          - assumption.
          - apply Succ.IsIncl. }
        assert (f:[a]: :<=: x) as H8. {
          intros y H8.
          apply (Bij.ImageCharac f (succ a) x a) in H8. 2: assumption.
          destruct H8 as [z [H8 [H9 H10]]]. rewrite <- H10.
          apply Bij.IsInRange with (succ a); assumption. }
        assert (exists m, Ordinal m /\ m :<=: x /\ f:[a]: :~: m) as H9. {
          apply SCE.OrdinalSubset; assumption. }
        destruct H9 as [m [H9 [H10 H11]]].
        assert (a :~: card a) as H12. {
          apply SCC.IsEquivGen. exists m. split. assumption.
          apply SCE.Tran with f:[a]:; assumption. }
        rewrite H3 in H12.
        apply H1. apply Finite.EquivCompat with :0:.
        - apply SCE.Sym. assumption.
        - apply Finite.WhenNat, Omega.HasZero. }
      rewrite H3, H4.
    + (* card a ≠ 0: a ~ card a by IsEquivNotZero.                              *)
      (* card a is an infinite ordinal: if card a < N then a ~ card a would be  *)
      (* finite, contradicting Infinite a. So N ⊆ card a and card a ~ succ(card a). *)
      (* Chain: a :\/: :{b}: ~ succ a ~ succ(card a) ~ card a.                  *)
      (* This gives card(a :\/: :{b}:) ≤ card a by IsLowerBound.                *)
      (* For the other direction, any bijection a :\/: :{b}: ~ c restricts to   *)
      (* a ~ f:[a]: ≤ c, giving an ordinal m ≤ c with a ~ m, so card a ≤ m ≤ c. *)
      assert (a :~: card a) as H4. { apply SCC.IsEquivNotZero. assumption. }
      assert (:N :<=: card a) as H5. {
        assert (card a :< :N \/ :N :<=: card a) as H5. {
          apply SOC.ElemOrIncl.
          - apply SCC.IsOrdinal.
          - apply Omega.IsOrdinal. }
        destruct H5 as [H5|H5]. 2: assumption. exfalso.
        apply H1. apply Finite.EquivCompat with (card a).
        - assumption.
        - apply Finite.WhenNat. assumption. }
      assert ((a :\/: :{b}:) :~: card a) as H6. {
        apply SCE.Tran with (succ a). 1: assumption.
        apply SCE.Tran with (succ (card a)).
        - apply SCE.SuccCompat. assumption.
        - apply SCE.Sym. apply SCE.Succ. apply SCC.IsOrdinal. assumption. }
      apply Incl.Double. split.
      * (* card(a :\/: :{b}:) ≤ card a: card a is an ordinal equivalent to     *)
        (* a :\/: :{b}: so it is a candidate for the infimum.                   *)
        apply SCC.IsLowerBound. apply SCC.IsOrdinal. assumption.
      * (* card a ≤ card(a :\/: :{b}:): for any ordinal c with                 *)
        (* a :\/: :{b}: ~ c, restrict to a to get ordinal m ≤ c with a ~ m,    *)
        (* hence card a ≤ m ≤ c.                                               *)
        apply SOI.IsLargest.
        -- intros c [H7 _]. assumption.
        -- apply CEM.HasElem. exists (card a). split. apply SCC.IsOrdinal. assumption.
        -- intros c [H7 H8]. destruct H8 as [f H8].
           assert (a :~: f:[a]:) as H9. {
             exists (f :|: a). apply Bij.Restrict with (a :\/: :{b}:) c.
             - assumption.
             - apply Union2.IsInclL. }
           assert (f:[a]: :<=: c) as H10. {
             intros y H10.
             apply (Bij.ImageCharac f (a :\/: :{b}:) c a) in H10. 2: assumption.
             destruct H10 as [z [H10 [H11 H12]]]. rewrite <- H12.
             apply Bij.IsInRange with (a :\/: :{b}:); assumption. }
           assert (exists m, Ordinal m /\ m :<=: c /\ f:[a]: :~: m) as H11. {
             apply SCE.OrdinalSubset; assumption. }
           destruct H11 as [m [H11 [H12 H13]]].
           apply Incl.Tran with m.
           ++ apply SCC.IsLowerBound. assumption.
              apply SCE.Tran with f:[a]:; assumption.
           ++ assumption.
Qed.
*)
