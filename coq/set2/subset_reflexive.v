Set Implicit Arguments.
Require Import Arith.

Require Import set.
Require Import order.
Require Import order_elements.
Require Import subset.
Require Import equiv.
Require Import subset_elements.

Proposition subset_reflexive : forall (a:set), subset a a.
Proof.
  (* induction on the order of a *)
  cut(forall (n:nat) (a:set), order a <= n -> subset a a).
  intros H a. apply H with (n:= order a). apply le_n. intro n. elim n.
  (* order a <= 0 *)
  intros a H. cut (a = Empty). intro H'. rewrite H'. unfold subset. simpl.
  reflexivity. apply order_eq_0. symmetry. apply le_n_0_eq. exact H.
  (* order a <= S n *)
  clear n. intros n IH a H. cut(order a < S n \/ order a = S n). intro H'. elim H'.
  (* order a < S n *)
  intro H''. unfold lt in H''. apply IH. apply le_S_n. exact H''.
  (* order a = S n *)
  intro H''. apply subset_elements. intros x Hx. exists x. split. exact Hx.
  unfold equiv. cut (subset x x). intro Hx'. split. exact Hx'. exact Hx'.

  apply IH. apply le_S_n. rewrite <- H''. apply order_elements.
  exact Hx.
  (* clean up *)
  apply le_lt_or_eq. exact H.
Qed.


