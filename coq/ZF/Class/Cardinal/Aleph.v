Require Import ZF.Class.Cardinal.Core.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Proper.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Omega.

Module CCC := ZF.Class.Cardinal.Core.

(* The class of infinite cardinal numbers.                                      *)
Definition InfiniteCard : Class := Cardinal :\: toClass :N.

(* The class of infinite cardinal numbers is a proper class.                    *)
Proposition IsProper : Proper InfiniteCard.
Proof.
  apply Diff.MinusASet, CCC.IsProper.
Qed.
