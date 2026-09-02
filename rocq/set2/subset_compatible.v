Require Import set.
Require Import subset.
Require Import equiv.
Require Import subset_transitive.

Proposition subset_compatible: forall (a a' b b':set),
  equiv a a' -> equiv b b' -> subset a b -> subset a' b'.
Proof.
  intros a a' b b' Eaa' Ebb' Hab.
  elim Eaa'. clear Eaa'. intros Haa' Ha'a.
  elim Ebb'. clear Ebb'. intros Hbb' Hb'b.
  apply subset_transitive with (b:=a). exact Ha'a. 
  apply subset_transitive with (b:=b). exact Hab. exact Hbb'.
Qed.

