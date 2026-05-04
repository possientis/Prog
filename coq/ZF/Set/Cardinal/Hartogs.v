Require Import ZF.Class.Cardinal.Hartogs.
Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Relation.Inj.


Module CCH := ZF.Class.Cardinal.Hartogs.

Definition hartogs (a:U) : U := fromClass (CCH.hartogs a) (CCH.IsSmall a).

Proposition ToClass : forall (a:U),
  toClass (hartogs a) :~: CCH.hartogs a.
Proof.
  intros a. apply FromClass.ToClass.
Qed.

Proposition Charac : forall (a x:U),
  x :< hartogs a <-> Ordinal x /\ exists f, Inj f x a.
Proof.
  intros a x. apply FromClass.Charac.
Qed.

Proposition IsOrdinal : forall (a:U), Ordinal (hartogs a).
Proof.
Admitted.


