Require Import set.
Require Import subset.
Require Import equiv.

Proposition single_compatible: forall (a a':set),
  equiv a a' -> equiv (Singleton a) (Singleton a'). 
Proof.
  intros a a' Eaa'. elim Eaa'. clear Eaa'. intros Haa' Ha'a.
  unfold equiv. split.
  apply subset_single_single. split. exact Haa'. exact Ha'a.
  apply subset_single_single. split. exact Ha'a. exact Haa'.
Qed.

