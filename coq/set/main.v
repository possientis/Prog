Set Implicit Arguments.
Require Import Bool.
Require Import Arith.
Require Import Arith.Max.
Require Import List.

Require Import set.
Require Import order.
Require Import subset.

(******************************************************************************)
(*                        equiv : set -> set -> Prop                         *)
(******************************************************************************)

Definition equiv (a b:set) : Prop := (subset a b) /\ (subset b a).

(******************************************************************************)
(*                        elements : set -> list set                          *)
(******************************************************************************)

Fixpoint elements (a:set) : list set :=
  match a with
    | Empty         => nil
    | Singleton x   => x::nil
    | Union x y     => (elements x) ++ (elements y) 
  end.

Lemma elements_order : forall (a x:set), In x (elements a) -> order x < order a.
Proof. intro a. elim a. (* induction on a*)
  (* a = Empty *)
  simpl. intro x. apply False_ind. 
  (* a = Singleton x *)
  clear a. intro x. intro H. clear H. intro z. simpl. intro H. elim H. intro H'.
  rewrite <- H'. unfold lt. apply le_n. apply False_ind. 
  (* a = Union x y *)
  clear a. intros x Hx y Hy z. simpl. intro H. 
  cut(In z (elements x) \/ In z (elements y)). intro H'. elim H'.

  intro Hx'. unfold lt. apply le_S. apply le_trans with (m:= order x). 
  apply Hx. exact Hx'. apply le_max_l.

  intro Hy'. unfold lt. apply le_S. apply le_trans with (m:= order y).
  apply Hy. exact Hy'. apply le_max_r. 

  apply in_app_or. exact H.
Qed.

Lemma subset_elements : forall (a b:set), subset a b <-> 
  forall (c:set), In c (elements a) -> exists (c':set), 
    In c' (elements b) /\  equiv c c'.  
Proof.
  (* Main induction on a, additional induction on b for a = Singleton x *)
  intro a. elim a. 
  (* a = Empty *)
  intros b. split. intros H c. clear H. simpl. apply False_ind.
  intros. apply subset_0_all.
  (* a = Singleton x *)
  clear a. intro x. intro IH. clear IH. intro b. elim b. 
  (* a = Singleton x, b = Empty *)
  split. intros H. apply False_ind. apply subset_single_0 with (x:=x). exact H.
  intro H. cut(exists c':set, In c' (elements Empty) /\ equiv x c'). 
  intro H'. simpl in H'. cut False. apply False_ind. elim H'.
  intros z H''. tauto. apply H. simpl. left. reflexivity.
  (* a = Singleton x, b = Singleton y *)
  clear b. intros y H. clear H. simpl. rewrite subset_single_single. 
  split.
  intro H. intros c H'. exists y. split. left. reflexivity. elim H'. intro H''.
  rewrite <- H''. unfold equiv. exact H.  apply False_ind.
  intro H. cut(exists c' : set, (y = c' \/ False) /\ equiv x c'). intro H'.
  elim H'. intro z. intro H''. elim H''. intros H0 H1. elim H0. intro H2.
  rewrite <- H2 in H1. exact H1. apply False_ind. apply H. left. reflexivity.
  (* a = Singleton x, b = Union y z *) 
  clear b. intros y Hy z Hz. rewrite subset_single_union. simpl. split.
  intros H c H'. elim H'. intro H''. rewrite <- H''. clear H''.
  cut(subset (Singleton x) y  \/ subset (Singleton x) z).
  intro H''. elim H''.

  intro Hy'. cut(exists c':set, In c' (elements y)/\equiv x c'). intro Hy''.
  elim Hy''. intro c'. intro Hc'. exists c'. split. elim Hc'. intro Hc''.
  intro H0. clear H0. apply in_or_app. left. exact Hc''. elim Hc'. intros H0 H1. 
  exact H1. apply Hy. exact Hy'. simpl. left. reflexivity. 
  
  intro Hz'. cut(exists c':set, In c' (elements z)/\equiv x c'). intro Hz''.
  elim Hz''. intro c'. intro Hc'. exists c'. split. elim Hc'. intro Hc''. intro H0.
  clear H0. apply in_or_app. right. exact Hc''. elim Hc'. intros H0 H1. exact H1.
  apply Hz. exact Hz'. simpl. left. reflexivity. 

  exact H. apply False_ind. intro H.
  
  cut(exists c' : set, In c' (elements y ++ elements z) /\ equiv x c').
  intro H'. elim H'. intros c' Hc'. elim Hc'. intros Hc'' Hc'''.
  cut(In c' (elements y) \/ In c' (elements z)). intro H0. elim H0. 
  
  intro H1. cut(subset (Singleton x) y). intro Hy'. left. exact Hy'.

  apply Hy. intros c Hc. 
  exists c'. split. exact H1. clear H1. simpl in Hc. elim Hc.
  intro H1. rewrite <- H1. exact Hc'''. apply False_ind. 

  intro H1. cut(subset (Singleton x) z). intro Hz'. right. exact Hz'.

  apply Hz. intros c Hc. 
  exists c'. split. exact H1. clear H1. simpl in Hc. elim Hc.
  intro H1. rewrite <- H1. exact Hc'''. apply False_ind. 

  apply in_app_or.  exact Hc''. apply H. left. reflexivity. 
  
  (* a = Union x y *) 
  clear a. intros x Hx y Hy b. split. intro H.
  rewrite subset_union_all in H. intro a. intro H'. simpl in H'.
  cut(In a (elements x) \/ In a (elements y)). intro Ha. elim Ha. 

  intro Ha'. apply Hx. apply proj1 with (B:= subset y b). 
  exact H. exact Ha'. 

  intro Ha'. apply Hy.  apply proj2 with (A:= subset x b). 
  exact H. exact Ha'. 

  apply in_app_or. exact H'. intro H. rewrite subset_union_all. split. 

  apply Hx. intros a Ha. apply H. simpl. apply in_or_app. left. exact Ha.
  apply Hy. intros a Ha. apply H. simpl. apply in_or_app. right. exact Ha.
Qed.


Lemma subset_reflexive : forall (a:set), subset a a.
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

  apply IH. apply le_S_n. rewrite <- H''. apply elements_order.
  exact Hx.
  (* clean up *)
  apply le_lt_or_eq. exact H.
Qed.

Lemma equiv_reflexive: forall (a:set), equiv a a.
Proof.
  intro a. unfold equiv. simpl. split. apply subset_reflexive.
  apply subset_reflexive.
Qed.

Lemma equiv_symmetric : forall (a b:set),
  equiv a b <-> equiv b a.
Proof.
  intros a b. unfold equiv. simpl. split. 
  intro H. split. 
  apply proj2 with (A:= subset a b). exact H.
  apply proj1 with (B:= subset b a). exact H.
  intro H. split.
  apply proj2 with (A:= subset b a). exact H.
  apply proj1 with (B:= subset a b). exact H.
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

Lemma subset_transitive: forall (a b c:set),
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
