Require Import ZF.Class.Cardinal.Hartogs.
Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.

Module CCH := ZF.Class.Cardinal.Hartogs.

Definition hartogs (a:U) : U := fromClass (CCH.hartogs a) (CCH.IsSmall a).

Proposition ToClass : forall (a:U),
  toClass (hartogs a) :~: CCH.hartogs a.
Proof.
  intros a. apply FromClass.ToFromClass.
Qed.
