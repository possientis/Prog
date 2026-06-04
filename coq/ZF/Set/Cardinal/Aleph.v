Require Import ZF.Class.Cardinal.Aleph.
Require Import ZF.Class.Cardinal.InfiniteCard.
Require Import ZF.Class.DiffBySet.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageUnderClass.

Module CCA := ZF.Class.Cardinal.Aleph.
Module CCI := ZF.Class.Cardinal.InfiniteCard.
Module SOC := ZF.Set.Ordinal.Core.
Module SOI := ZF.Set.Ordinal.InfOfClass.

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
    apply ImageUnderClass.WhenEmpty. reflexivity. }
  rewrite H1, H2. transitivity (inf InfiniteCard).
  - apply SOI.EquivCompat. apply DiffBySet.IdentityR.
  - apply CCI.Inf.
Qed.
