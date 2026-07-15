Require Import ZF.Class.Cardinal.Aleph.
Require Import ZF.Class.Cardinal.InfiniteCard.
Require Import ZF.Class.DiffBySet.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Monotone.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Cofinal.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Monotone.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.ImageUnderClass.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.UnionGenOfClass.

Module CCA := ZF.Class.Cardinal.Aleph.
Module CCI := ZF.Class.Cardinal.InfiniteCard.
Module CFL := ZF.Class.Relation.Functional.
Module CFO := ZF.Class.Relation.FunctionOn.
Module COM := ZF.Class.Ordinal.Monotone.
Module SOC := ZF.Set.Ordinal.Core.
Module SOM := ZF.Set.Ordinal.Monotone.
Module SOI := ZF.Set.Ordinal.InfOfClass.
Module SUG := ZF.Set.UnionGenOfClass.

(* The isomorphism between the ordinals and infinite cardinals evaluated at a.  *)
Definition aleph (a:U) : U := CCA.Aleph!a.

Proposition IsIncl : forall (a:U), Ordinal a ->
  a :<=: aleph a.
Proof.
  apply CCA.IsIncl.
Qed.

(* The zeroth infinite cardinal is omega.                                       *)
Proposition WhenZero : aleph :0: = :N.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* aleph(0) is the infimum of the infinite cardinals not in the image         *)
  (* aleph[0]. Since 0 is the empty set, the image aleph[0] is empty, and       *)
  (* the infimum reduces to that of all infinite cardinals, which is omega.     *)
  unfold aleph.
  assert (CCA.Aleph!:0: = inf (InfiniteCard :\: CCA.Aleph:[:0:]:)) as H1. {
    apply CCA.IsInf. apply SOC.Zero. }
  assert (CCA.Aleph:[:0:]: = :0:) as H2. {
    apply ImageUnderClass.WhenZero. reflexivity. }
  rewrite H1, H2. transitivity (inf InfiniteCard).
  - apply SOI.EquivCompat. apply DiffBySet.IdentityR.
  - apply CCI.Inf.
Qed.

(* At a limit index, the corresponding aleph is cofinal with that index.        *)
Proposition WhenLimit : forall (a:U), Limit a -> Cofinal (aleph a) a.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1.
  assert (Ordinal a) as H2. { apply H1. }
  remember (CCA.Aleph:|:a) as f eqn:Hf.
  split.
  - (* Every index lies below its aleph value.                                  *)
    apply IsIncl. assumption.
  - exists f.
    assert (SOM.Monotone f) as H3. {
      rewrite Hf.
      apply SOM.ClassRestrict. 1: assumption.
      - apply CCA.IsMonotone.
      - intros x H3. apply CCA.DomainOf.
        apply (SOC.IsOrdinal a); assumption. }
    split. 1: assumption.
    assert (CFO.FunctionOn Aleph Ordinal) as G2. { apply CCA.IsFunctionOn. }
    assert (Fun f a (aleph a)) as H4. {
      split.
      - rewrite Hf. apply RestrictOfClass.IsFunctionOn. 1: apply G2.
        intros x H4. apply CCA.DomainOf. apply (SOC.IsOrdinal a); assumption.
      - intros y H4.
        assert (CFL.Functional CCA.Aleph) as G1. { apply G2. }
        rewrite Hf in H4. rewrite RestrictOfClass.RangeOf in H4. 2: assumption.
        apply ImageUnderClass.Charac in H4. 2: assumption.
        destruct H4 as [x [H4 H5]].
        assert (Ordinal x) as H6. { apply (SOC.IsOrdinal a); assumption. }
        assert (CCA.Aleph!x = y) as H7. {
          apply (CFO.Eval CCA.Aleph Ordinal);
          try apply CCA.IsFunctionOn; assumption. }
        rewrite <- H7.
        assert (COM.Monotone CCA.Aleph) as H8. { apply CCA.IsMonotone. }
        destruct H8 as [_ H8].
        assert (CCA.Aleph!x :< CCA.Aleph!a) as H9. {
          apply H8; try apply CCA.DomainOf; assumption. }
        assumption. }
    split. 1: assumption. intros c H5.
    (* Continuity turns any smaller ordinal into a value below some earlier     *)
    (* aleph, and the restricted Aleph map supplies that value.                 *)
    assert (aleph a = :\/:_{a} CCA.Aleph) as H6. {
      apply CCA.WhenLimit. assumption. }
    rewrite H6 in H5.
    apply SUG.Charac in H5. destruct H5 as [d [H7 H8]].
    exists d. split. 1: assumption.
    assert (Ordinal d) as H9. { apply (SOC.IsOrdinal a); assumption. }
    assert (f!d = CCA.Aleph!d) as H10. {
      rewrite Hf. apply RestrictOfClass.Eval. 2: assumption. apply G2. }
    rewrite H10. apply SOC.ElemIsIncl. 2: assumption.
    apply CCI.IsOrdinal, CCA.IsInfiniteCard. assumption.
Qed.
