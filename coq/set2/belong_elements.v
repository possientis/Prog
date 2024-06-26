Require Import List.

Require Import set.
Require Import elements.
Require Import subset.
Require Import belong.
Require Import equiv.
Require Import subset_elements.
Require Import equiv_reflexive.


Proposition belong_elements : forall (a b: set),
  belong a b <-> exists (c:set), In c (elements b) /\ equiv a c.
Proof.
  intros a b. split. intros Bab. unfold belong in Bab. 
  rewrite subset_elements in Bab. apply Bab.
  unfold elements. simpl. left. reflexivity.
  intros H. unfold belong. apply subset_elements.
  intros x Exa. elim H. clear H. intros c Hc. exists c.
  unfold elements in Exa. simpl in Exa. elim Exa. clear Exa.
  intros Eax. rewrite <- Eax. exact Hc. apply False_ind.
Qed.

Corollary element_imp_belong: forall (a b:set),
  In a (elements b) -> belong a b.
Proof.
  intros a b Hab. apply belong_elements. exists a.
  split. exact Hab. apply equiv_reflexive.
Qed.
