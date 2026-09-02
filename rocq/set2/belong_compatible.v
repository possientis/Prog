Require Import set.
Require Import subset.
Require Import belong.
Require Import equiv.
Require Import single_compatible.
Require Import subset_compatible.

Proposition belong_compatible: forall (a a' b b':set),
  equiv a a' -> equiv b b' -> belong a b -> belong a' b'.
Proof.
  intros a a' b b' Eaa' Ebb' Hab.
  unfold belong. apply subset_compatible with (a:= (Singleton a))(b:= b).
  apply single_compatible. exact Eaa'. exact Ebb'. exact Hab.
Qed.

