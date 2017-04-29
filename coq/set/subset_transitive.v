Set Implicit Arguments.

Require Import Arith.
Require Import Arith.Max.
Require Import List.

Require Import set.
Require Import order.
Require Import subset.
Require Import equiv.
Require Import elements.
Require Import subset_reflexive.
Require Import equiv_reflexive.
Require Import equiv_symmetric.

Proposition subset_transitive: forall (a b c:set),
  subset a b -> subset b c -> subset a c.
Proof. 
  (* by induction on n = max(order a, order b, order c) *)
  (*set up induction on n *)
  cut(forall (n:nat)(a b c:set), order a <= n -> order b <= n -> order c <= n ->  
    subset a b -> subset b c -> subset a c). intros H a b c.
  pose (n:= max (order a) (max (order b) (order c))). apply H with (n:=n).
  change (order a <= max (order a) (max (order b) (order c))). apply le_max_l.
  apply le_trans with (m:= max (order b) (order c)). apply le_max_l.
  change (max (order b) (order c) <= max (order a) (max (order b) (order c))).
  apply le_max_r. apply le_trans with(m:=max (order b) (order c)). apply le_max_r. 
  change (max (order b) (order c) <= max (order a) (max (order b) (order c))).
  apply  le_max_r. intro n. elim n.
  (* n = 0 *)
  intros a b c Ha Hb Hc Hab Hbc. clear Hb Hc Hab Hbc. cut (a = Empty). intro H. 
  rewrite H. apply subset_0_all. apply order_eq_0. symmetry. apply le_n_0_eq.
  exact Ha.
  (* n => n+1 *)
  clear n. intros n IH. intros a b c Ha Hb Hc Hab Hbc. apply subset_elements.
  intros x Hx. cut (exists y:set, In y (elements b) /\ equiv x y). 
  intro H. elim H. intros y Hy.
  cut (exists z:set, In z (elements c) /\ equiv y z). intro H'. elim H'.
  intros z Hz. exists z. split. elim Hz. auto. unfold equiv.
  split.

  apply IH with (b:=y). 
  apply le_S_n. apply le_trans with (m:= order a). apply elements_order. exact Hx. 
  exact Ha. 
  apply le_S_n. apply le_trans with (m:=order b). apply elements_order. elim Hy.
  auto. exact Hb.
  apply le_S_n. apply le_trans with (m:= order c). apply elements_order. elim Hz.
  auto. exact Hc.
 
  elim Hy. intros H0 EQxy. clear H0. unfold equiv in EQxy. 
  apply proj1 with (B:= subset y x). exact EQxy. 

  elim Hz. intros H0 EQyz. clear H0. unfold equiv in EQyz. 
  apply proj1 with (B:= subset z y). exact EQyz.

  apply IH with (b:=y).
  apply le_S_n. apply le_trans with (m:= order c). apply elements_order. elim Hz.
  auto. exact Hc.
  apply le_S_n. apply le_trans with (m:= order b). apply elements_order. elim Hy.
  auto. exact Hb.
  apply le_S_n. apply le_trans with (m:= order a). apply elements_order. exact Hx.
  exact Ha.
  
  elim Hz. intros H0 EQyz. clear H0. unfold equiv in EQyz. 
  apply proj2 with (A:= subset y z). exact EQyz.

  elim Hy. intros H0 EQxy. clear H0. unfold equiv in EQxy. 
  apply proj2 with (A:= subset x y). exact EQxy.
 
  apply subset_elements with (a:=b). exact Hbc. elim Hy. auto.
  apply subset_elements with (a:=a). exact Hab. exact Hx.
Qed.

Lemma subset_x_xUy : forall (x y: set), subset x (Union x y).
Proof.
  intros x y. apply subset_elements. intros z H. exists z. split. simpl.
  apply in_or_app. left. exact H. apply equiv_reflexive.
Qed.

Lemma subset_y_xUy : forall (x y: set), subset y (Union x y).
Proof.
  intros x y. apply subset_elements. intros z H. exists z. split. simpl.
  apply in_or_app. right. exact H. apply equiv_reflexive.
Qed.

Lemma subset_xUy : forall (x y: set), subset (Union x y) (Union y x).
Proof.
  intros x y. apply subset_elements. intros z H. exists z. split. simpl.
  simpl in H. apply in_or_app.  apply or_comm. apply in_app_or. exact H. 
  apply equiv_reflexive.
Qed.

Lemma subset_xUyUz_l : forall (x y z:set),
  subset (Union (Union x y) z) (Union x (Union y z)).
Proof.
  intros x y z. apply subset_elements. simpl. intros t H. exists t. split.
  rewrite app_assoc. exact H. apply equiv_reflexive.
Qed.

Lemma subset_xUyUz_r : forall (x y z:set),
  subset (Union x (Union y z)) (Union (Union x y) z).
Proof.
  intros x y z. apply subset_elements. simpl. intros t H. exists t. split.
  rewrite app_assoc in H. exact H. apply equiv_reflexive.
Qed.

Lemma equiv_xUyUz_l : forall (x y z:set),
  equiv (Union (Union x y) z) (Union x (Union y z)).
Proof.
  intros x y z. unfold equiv. simpl. split.
  apply subset_xUyUz_l. apply subset_xUyUz_r.
Qed.

Lemma equiv_xUyUz_r : forall (x y z:set),
  equiv (Union x (Union y z)) (Union (Union x y) z).
Proof.
  intros x y z. apply equiv_symmetric. apply equiv_xUyUz_l.
Qed.

Lemma subset_xU0_x : forall (x:set), subset (Union x Empty) x.
Proof.
  intro x. rewrite subset_union_all. split. apply subset_reflexive.
  apply subset_0_all. 
Qed.

Lemma subset_x_xU0 : forall (x:set), subset x (Union x Empty).
Proof.
  intro x. apply subset_x_xUy.
Qed.

Lemma equiv_xU0_x: forall (x:set), equiv (Union x Empty) x.
Proof.
  intro x. unfold equiv. split. apply subset_xU0_x. apply subset_x_xU0.
Qed.


