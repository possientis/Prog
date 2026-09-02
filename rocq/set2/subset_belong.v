Require Import List.

Require Import set.
Require Import elements.
Require Import subset.
Require Import belong.
Require Import equiv.
Require Import subset_elements.
Require Import belong_elements.
Require Import equiv_transitive.

Proposition subset_belong: forall (a b:set),
  subset a b <-> forall (x:set), belong x a -> belong x b.
Proof.
  intros a b. split. intros Hab x Hxa. apply belong_elements.
  apply belong_elements in Hxa. elim Hxa. clear Hxa. intros y Hya.
  elim Hya. clear Hya. intros Hya Exy.
  rewrite subset_elements in Hab. elim (Hab y). clear Hab. intros z Hzb.
  elim Hzb. clear Hzb. intros Hzb Eyz. exists z. split. exact Hzb.
  apply equiv_transitive with (b:= y). exact Exy. exact Eyz. exact Hya. 

  intros H. apply subset_elements. intros x Hxa.
  apply belong_elements. apply H. apply element_imp_belong. exact Hxa.
Qed.
