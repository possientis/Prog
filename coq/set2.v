Require Import set. (* need to compile set.v *)
Require Import Bool.
Require Import Arith.
Require Import Arith.Max.
Require Import List.

(* replicating proof of set.v with 'Prop' instead of 'bool' *)

(******************************************************************************)
(*                       subset2 : set -> set -> Prop                         *)
(******************************************************************************)

Fixpoint subset2_n (n:nat) : set -> set -> Prop :=
  match n with 
    | 0   => (fun _ _     => True)
    | S p => (fun a b     =>
      match a with
        | Empty           => True
        | Singleton x     => 
          match b with
            | Empty       => False
            | Singleton y => subset2_n p x y /\ subset2_n p y x
            | Union y z   => subset2_n p (Singleton x) y \/
                             subset2_n p (Singleton x) z 
          end
        | Union x y       => subset2_n p x b /\ subset2_n p y b
      end)
  end.

(* making sure the two points of view are equivalent *)
Lemma subset_n_bool_prop : forall (n:nat)(a b:set),
  subset2_n n a b <-> subset_n n a b = true.
Proof. 
  (* induction on n *)
  intro n. elim n. 
  (* n = 0 *)
  intros a b. simpl. tauto.
  (* n -> n+1 *) (* induction on a *)
  clear n. intros n IH. intro a. elim a.
  (* a = Empty *)
  intro b. simpl. tauto.
  (* a = Singleton x *)(* induction on b *)
  clear a. intros x IH'. intro b. elim b.
  (* b = Empty *)
  simpl. split. apply False_ind. intro H. discriminate H. 
  (* b = Singleton y *)
  clear b. intros y IH''. simpl. split. intro H.
  apply andb_true_iff. split. apply IH. tauto. apply IH. tauto.

  intro H. split. 
  apply IH. apply proj1 with (B:= subset_n n y x = true). 
  apply andb_true_iff. exact H. 

  apply IH. apply proj2 with (A:= subset_n n x y = true).
  apply andb_true_iff. exact H.
  (* b = Union y z *)
  clear b. intros y IHy z IHz. simpl. split. intro H. apply orb_true_iff. elim H.
  intro Hy'. left. apply IH. exact Hy'.
  intro Hz'. right. apply IH. exact Hz'.
  intro H. rewrite orb_true_iff in H. elim H.
  intro Hy'. left. apply IH. exact Hy'.
  intro Hz'. right. apply IH. exact Hz'.
  (* a = Union x y *)
  clear a. intros x Hx y Hy b. simpl. rewrite andb_true_iff.
  rewrite IH with (a:=x)(b:=b). rewrite IH with (a:=y)(b:=b). tauto.
Qed.

Lemma subset2_n_Sn : forall (n:nat) (a b:set),
  order a + order b <= n -> (subset2_n n a b <-> subset2_n (S n) a b).
Proof. 
  (* induction on n *)
  intro n. elim n.
  (* n = 0 *)
  intros a b. intro H. cut(a = Empty). intro H'. rewrite H'. simpl. tauto.
  apply order_sum_eq_0_l with (b:=b). symmetry. apply le_n_0_eq. exact H.
  (* n -> n+1 *)(* induction on a *)
  clear n. intros n IH. intro a. elim a.
  (* a = Empty *)
  intro b. simpl. tauto.
  (* a = Singleton x *)(* induction on b *)
  clear a. intros x Hx. intro b. elim b.
  (* b = Empty *)
  intro H. simpl. tauto.
  (* b = Singleton y *)
  clear b. intros y Hy H.
  unfold subset2_n at 1. fold subset2_n.
  cut(subset2_n (S (S n)) (Singleton x) (Singleton y) <-> 
     (subset2_n (S n) x y)/\(subset2_n (S n) y x)). 
  intro H'. rewrite H'. rewrite <- IH, <- IH. tauto.
  apply order_sum_singleton. rewrite plus_comm. exact H.
  apply order_sum_singleton. exact H.
  simpl. reflexivity.
  (* b = Union y z *)
  clear b. intros y Hy z Hz H.
  unfold subset2_n at 1. fold subset2_n.
  cut(subset2_n (S (S n)) (Singleton x) (Union y z) <->
     (subset2_n (S n) (Singleton x) y)\/(subset2_n (S n) (Singleton x) z)).
  intro H'. rewrite H'. rewrite <- IH, <- IH. tauto.
  apply order_sum_union_Rr with (y:=y). exact H.
  apply order_sum_union_Rl with (z:=z). exact H. 
  simpl. reflexivity.
  (* a = Union x y *)
  clear a. intros x Hx y Hy b H.
  unfold subset2_n at 1. fold subset2_n.
  cut(subset2_n (S (S n)) (Union x y) b <-> 
     (subset2_n (S n) x b)/\(subset2_n (S n) y b)).
  intro H'. rewrite H'. rewrite <- IH, <- IH. tauto.
  apply order_sum_union_Lr with (x:=x). exact H.
  apply order_sum_union_Ll with (y:=y). exact H.
  simpl. reflexivity.
  Qed.

Definition subset2 (a b:set) : Prop :=
  let n:= order a + order b in subset2_n n a b.

(* making sure the two points of view are equivalent *)
Lemma subset_bool_prop : forall (a b:set),
  subset2 a b <-> subset a b = true.
Proof.
  intros a b. unfold subset2, subset. apply subset_n_bool_prop.
Qed.

Lemma subset2_subset2_n : forall (n:nat) (a b:set),
  order a + order b <= n -> (subset2 a b <-> subset2_n n a b).
Proof.
  (* induction on n *)
  intros n. elim n.
  (* n = 0 *)
  intros a b H. cut (a = Empty). cut (b = Empty). intros Hb Ha. rewrite Ha, Hb.
  unfold subset2. simpl. tauto.
  apply order_sum_eq_0_r with (a:=a). symmetry. apply le_n_0_eq. exact H.
  apply order_sum_eq_0_l with (b:=b). symmetry. apply le_n_0_eq. exact H.
  (* n -> n+1 *)
  clear n. intros n IH a b H.
  (* either order a + order b < S n or = S n *)
  cut((order a + order b < S n)\/(order a + order b = S n)). intro H0. elim H0.
  (* order a + order b < S n *)
  intro H1. rewrite IH. apply subset2_n_Sn. 
  apply le_S_n. exact H1. apply le_S_n. exact H1. 
  (* order a + order b = S n *)
  intro H1. unfold subset2. rewrite H1. tauto.
  (* finally *)
  apply le_lt_or_eq. exact H.
Qed.

Lemma subset2_0_all : forall (b:set), subset2 Empty b.
Proof.
  (* induction on b *)
  intro b. elim b.
  (* b = Empty *)
  unfold subset2. simpl. apply I.
  (* b = Singleton x *)
  clear b. intros x H. unfold subset2. simpl. apply I.
  (* b = Union x y *)
  clear b. intros x Hx y Hy. unfold subset2. simpl. apply I.
Qed.

Lemma subset2_single_0 : forall (x:set), ~subset2 (Singleton x) Empty.
Proof.
  (* not structural induction necessary *)
  intro x. unfold subset2. simpl. tauto.
Qed.


Lemma subset2_single_single : forall (x y:set),
  subset2 (Singleton x) (Singleton y) <-> (subset2 x y)/\(subset2 y x).
Proof.
  intros x y. unfold subset2 at 1. simpl. 
  rewrite <- subset2_subset2_n, <- subset2_subset2_n. tauto.
  rewrite plus_comm. apply plus_le_compat_l. apply le_S. apply le_n.
  apply plus_le_compat_l. apply le_S. apply le_n.
Qed.

Lemma subset2_single_union: forall (x y z:set),
  subset2 (Singleton x) (Union y z) <-> 
  (subset2 (Singleton x) y)\/(subset2 (Singleton x) z).
Proof.
  intros x y z. unfold subset2 at 1. simpl.
  rewrite <- subset2_subset2_n, <- subset2_subset2_n. tauto. 
  simpl. rewrite <- plus_n_Sm. apply le_n_S. 
  apply plus_le_compat_l. apply le_max_r.
  simpl. rewrite <- plus_n_Sm. apply le_n_S. 
  apply plus_le_compat_l. apply le_max_l.
Qed.

Lemma subset2_union_all : forall (x y b:set),
  subset2 (Union x y) b <-> (subset2 x b)/\(subset2 y b).
Proof.
  intros x y b. unfold subset2 at 1. simpl.
  rewrite <- subset2_subset2_n, <- subset2_subset2_n. tauto.
  apply plus_le_compat_r. apply le_max_r. apply plus_le_compat_r. apply le_max_l.
Qed.

Definition subset2_prop_1 (relation: set -> set -> Prop) : Prop :=
  forall (b:set), relation Empty b.

Definition subset2_prop_2 (relation: set -> set -> Prop) : Prop :=
  forall (x:set), ~relation (Singleton x) Empty.

Definition subset2_prop_3 (relation: set-> set -> Prop) : Prop :=
  forall (x y:set),
  relation (Singleton x) (Singleton y) <-> relation x y /\ relation y x.

Definition subset2_prop_4 (relation: set -> set -> Prop) : Prop :=
  forall (x y z:set),
  relation (Singleton x) (Union y z) <->
  relation (Singleton x) y \/ relation (Singleton x) z.

Definition subset2_prop_5 (relation: set -> set -> Prop) : Prop :=
  forall (x y b:set),
  relation (Union x y) b <-> relation x b /\ relation y b.

Lemma subset2_exist :
  subset2_prop_1 subset2 /\
  subset2_prop_2 subset2 /\
  subset2_prop_3 subset2 /\
  subset2_prop_4 subset2 /\
  subset2_prop_5 subset2.
Proof.
  split. unfold subset2_prop_1. apply subset2_0_all.
  split. unfold subset2_prop_2. apply subset2_single_0.
  split. unfold subset2_prop_3. apply subset2_single_single.
  split. unfold subset2_prop_4. apply subset2_single_union.
  unfold subset2_prop_5. apply subset2_union_all.
Qed.

(* subset2 is the unique relation on set satisfying properties 1-5 *) 
Lemma subset2_unique : forall (relation : set -> set -> Prop),
  subset2_prop_1 relation ->
  subset2_prop_2 relation ->
  subset2_prop_3 relation ->
  subset2_prop_4 relation ->
  subset2_prop_5 relation ->
  forall (a b:set), relation a b <-> subset2 a b.
Proof.
  intros relation H1 H2 H3 H4 H5 a b.
  (* proof by induction on order a + order b <= n *)
  cut(forall n:nat, order a + order b <= n -> (relation a b <-> subset2 a b)).
  intro H. apply H with (n:= order a + order b). apply le_n.
  intro n. generalize a b. clear a b. elim n.
  (* order a + order b <= 0 *) 
  intros a b H. cut (a = Empty). intro H'. rewrite H'.
  split. intros. apply subset2_0_all. intros. apply H1.
  apply order_sum_eq_0_l with (b:=b). symmetry. apply le_n_0_eq. exact H.
  (* true for <= n -> true for <= n+1 *)
  (* induction on a *)  
  clear n. intros n IH a. elim a.
  (* a = Empty *)
  intros b H. split. intros. apply subset2_0_all. intros. apply H1.
  (* a = Singleton x *)(* induction on b *)
  clear a. intros x H b. elim b.
  (* b = Empty *)
  intros. split. 
  intros. apply False_ind. apply H2 with (x:=x). exact H6.
  intros. apply False_ind. apply subset2_single_0 with (x:=x). exact H6. 
  (* b = Singleton y *)
  clear b. intros y H' H''. unfold subset2_prop_3 in H3. 
  rewrite H3, subset2_single_single, IH, IH. tauto.
  rewrite plus_comm. apply order_sum_singleton. exact H''.
  apply order_sum_singleton. exact H''.
  (* b = Union y z *)
  clear b. intros y Hy z Hz H'. unfold subset2_prop_4 in H4.
  rewrite H4, subset2_single_union, IH, IH. tauto.
  apply order_sum_union_Rr with (y:=y). exact H'.
  apply order_sum_union_Rl with (z:=z). exact H'.
  (* a = Union x y *)
  clear a. intros x Hx y Hy b H. unfold subset2_prop_5 in H5.
  rewrite H5, subset2_union_all, IH, IH. tauto.
  apply order_sum_union_Lr with (x:=x). exact H.
  apply order_sum_union_Ll with (y:=y). exact H.
Qed.

(******************************************************************************)
(*                        equiv2 : set -> set -> Prop                         *)
(******************************************************************************)

Definition equiv2 (a b:set) : Prop := (subset2 a b) /\ (subset2 b a).


Lemma subset2_elements : forall (a b:set), subset2 a b <-> 
  forall (c:set), In c (elements a) -> exists (c':set), 
    In c' (elements b) /\  equiv2 c c'.  
Proof.
  (* Main induction on a, additional induction on b for a = Singleton x *)
  intro a. elim a. 
  (* a = Empty *)
  intros b. split. intros H c. clear H. simpl. apply False_ind.
  intros. apply subset2_0_all.
  (* a = Singleton x *)
  clear a. intro x. intro IH. clear IH. intro b. elim b. 
  (* a = Singleton x, b = Empty *)
  split. intros H. apply False_ind. apply subset2_single_0 with (x:=x). exact H.
  intro H. cut(exists c':set, In c' (elements Empty) /\ equiv2 x c'). 
  intro H'. simpl in H'. cut False. apply False_ind. elim H'.
  intros z H''. tauto. apply H. simpl. left. reflexivity.
  (* a = Singleton x, b = Singleton y *)
  clear b. intros y H. clear H. simpl. rewrite subset2_single_single. 
  split.
  intro H. intros c H'. exists y. split. left. reflexivity. elim H'. intro H''.
  rewrite <- H''. unfold equiv. exact H.  apply False_ind.
  intro H. cut(exists c' : set, (y = c' \/ False) /\ equiv2 x c'). intro H'.
  elim H'. intro z. intro H''. elim H''. intros H0 H1. elim H0. intro H2.
  rewrite <- H2 in H1. exact H1. apply False_ind. apply H. left. reflexivity.
  (* a = Singleton x, b = Union y z *) 
  clear b. intros y Hy z Hz. rewrite subset2_single_union. simpl. split.
  intros H c H'. elim H'. intro H''. rewrite <- H''. clear H''.
  cut(subset2 (Singleton x) y  \/ subset2 (Singleton x) z).
  intro H''. elim H''.

  intro Hy'. cut(exists c':set, In c' (elements y)/\equiv2 x c'). intro Hy''.
  elim Hy''. intro c'. intro Hc'. exists c'. split. elim Hc'. intro Hc''.
  intro H0. clear H0. apply in_or_app. left. exact Hc''. elim Hc'. intros H0 H1. 
  exact H1. apply Hy. exact Hy'. simpl. left. reflexivity. 
  
  intro Hz'. cut(exists c':set, In c' (elements z)/\equiv2 x c'). intro Hz''.
  elim Hz''. intro c'. intro Hc'. exists c'. split. elim Hc'. intro Hc''. intro H0.
  clear H0. apply in_or_app. right. exact Hc''. elim Hc'. intros H0 H1. exact H1.
  apply Hz. exact Hz'. simpl. left. reflexivity. 

  exact H. apply False_ind. intro H.
  
  cut(exists c' : set, In c' (elements y ++ elements z) /\ equiv2 x c').
  intro H'. elim H'. intros c' Hc'. elim Hc'. intros Hc'' Hc'''.
  cut(In c' (elements y) \/ In c' (elements z)). intro H0. elim H0. 
  
  intro H1. cut(subset2 (Singleton x) y). intro Hy'. left. exact Hy'.

  apply Hy. intros c Hc. 
  exists c'. split. exact H1. clear H1. simpl in Hc. elim Hc.
  intro H1. rewrite <- H1. exact Hc'''. apply False_ind. 

  intro H1. cut(subset2 (Singleton x) z). intro Hz'. right. exact Hz'.

  apply Hz. intros c Hc. 
  exists c'. split. exact H1. clear H1. simpl in Hc. elim Hc.
  intro H1. rewrite <- H1. exact Hc'''. apply False_ind. 

  apply in_app_or.  exact Hc''. apply H. left. reflexivity. 
  
  (* a = Union x y *) 
  clear a. intros x Hx y Hy b. split. intro H.
  rewrite subset2_union_all in H. intro a. intro H'. simpl in H'.
  cut(In a (elements x) \/ In a (elements y)). intro Ha. elim Ha. 

  intro Ha'. apply Hx. apply proj1 with (B:= subset2 y b). 
  exact H. exact Ha'. 

  intro Ha'. apply Hy.  apply proj2 with (A:= subset2 x b). 
  exact H. exact Ha'. 

  apply in_app_or. exact H'. intro H. rewrite subset2_union_all. split. 

  apply Hx. intros a Ha. apply H. simpl. apply in_or_app. left. exact Ha.
  apply Hy. intros a Ha. apply H. simpl. apply in_or_app. right. exact Ha.
Qed.


Lemma subset2_reflexive : forall (a:set), subset2 a a.
Proof.
  (* induction on the order of a *)
  cut(forall (n:nat) (a:set), order a <= n -> subset2 a a).
  intros H a. apply H with (n:= order a). apply le_n. intro n. elim n.
  (* order a <= 0 *)
  intros a H. cut (a = Empty). intro H'. rewrite H'. unfold subset2. simpl.
  reflexivity. apply order_eq_0. symmetry. apply le_n_0_eq. exact H.
  (* order a <= S n *)
  clear n. intros n IH a H. cut(order a < S n \/ order a = S n). intro H'. elim H'.
  (* order a < S n *)
  intro H''. unfold lt in H''. apply IH. apply le_S_n. exact H''.
  (* order a = S n *)
  intro H''. apply subset2_elements. intros x Hx. exists x. split. exact Hx.
  unfold equiv2. cut (subset2 x x). intro Hx'. split. exact Hx'. exact Hx'.

  apply IH. apply le_S_n. rewrite <- H''. apply elements_order.
  exact Hx.
  (* clean up *)
  apply le_lt_or_eq. exact H.
Qed.

Lemma equiv2_reflexive: forall (a:set), equiv2 a a.
Proof.
  intro a. unfold equiv2. simpl. split. apply subset2_reflexive.
  apply subset2_reflexive.
Qed.

Lemma equiv2_symmetric : forall (a b:set),
  equiv2 a b <-> equiv2 b a.
Proof.
  intros a b. unfold equiv2. simpl. split. 
  intro H. split. 
  apply proj2 with (A:= subset2 a b). exact H.
  apply proj1 with (B:= subset2 b a). exact H.
  intro H. split.
  apply proj2 with (A:= subset2 b a). exact H.
  apply proj1 with (B:= subset2 a b). exact H.
Qed.

Lemma subset2_x_xUy : forall (x y: set), subset2 x (Union x y).
Proof.
  intros x y. apply subset2_elements. intros z H. exists z. split. simpl.
  apply in_or_app. left. exact H. apply equiv2_reflexive.
Qed.

Lemma subset2_y_xUy : forall (x y: set), subset2 y (Union x y).
Proof.
  intros x y. apply subset2_elements. intros z H. exists z. split. simpl.
  apply in_or_app. right. exact H. apply equiv2_reflexive.
Qed.

Lemma subset2_xUy : forall (x y: set), subset2 (Union x y) (Union y x).
Proof.
  intros x y. apply subset2_elements. intros z H. exists z. split. simpl.
  simpl in H. apply in_or_app.  apply or_comm. apply in_app_or. exact H. 
  apply equiv2_reflexive.
Qed.

Lemma subset2_xUyUz_l : forall (x y z:set),
  subset2 (Union (Union x y) z) (Union x (Union y z)).
Proof.
  intros x y z. apply subset2_elements. simpl. intros t H. exists t. split.
  rewrite app_assoc. exact H. apply equiv2_reflexive.
Qed.

Lemma subset2_xUyUz_r : forall (x y z:set),
  subset2 (Union x (Union y z)) (Union (Union x y) z).
Proof.
  intros x y z. apply subset2_elements. simpl. intros t H. exists t. split.
  rewrite app_assoc in H. exact H. apply equiv2_reflexive.
Qed.

Lemma equiv2_xUyUz_l : forall (x y z:set),
  equiv2 (Union (Union x y) z) (Union x (Union y z)).
Proof.
  intros x y z. unfold equiv2. simpl. split.
  apply subset2_xUyUz_l. apply subset2_xUyUz_r.
Qed.

Lemma equiv2_xUyUz_r : forall (x y z:set),
  equiv2 (Union x (Union y z)) (Union (Union x y) z).
Proof.
  intros x y z. apply equiv2_symmetric. apply equiv2_xUyUz_l.
Qed.

Lemma subset2_xU0_x : forall (x:set), subset2 (Union x Empty) x.
Proof.
  intro x. rewrite subset2_union_all. split. apply subset2_reflexive.
  apply subset2_0_all. 
Qed.

Lemma subset2_x_xU0 : forall (x:set), subset2 x (Union x Empty).
Proof.
  intro x. apply subset2_x_xUy.
Qed.

Lemma equiv2_xU0_x: forall (x:set), equiv2 (Union x Empty) x.
Proof.
  intro x. unfold equiv2. split. apply subset2_xU0_x. apply subset2_x_xU0.
Qed.

Lemma subset2_transitive: forall (a b c:set),
  subset2 a b -> subset2 b c -> subset2 a c.
Proof. 
  (* by induction on n = max(order a, order b, order c) *)
  (*set up induction on n *)
  cut(forall (n:nat)(a b c:set), order a <= n -> order b <= n -> order c <= n ->  
    subset2 a b -> subset2 b c -> subset2 a c). intros H a b c.
  pose (n:= max (order a) (max (order b) (order c))). apply H with (n:=n).
  change (order a <= max (order a) (max (order b) (order c))). apply le_max_l.
  apply le_trans with (m:= max (order b) (order c)). apply le_max_l.
  change (max (order b) (order c) <= max (order a) (max (order b) (order c))).
  apply le_max_r. apply le_trans with(m:=max (order b) (order c)). apply le_max_r. 
  change (max (order b) (order c) <= max (order a) (max (order b) (order c))).
  apply  le_max_r. intro n. elim n.
  (* n = 0 *)
  intros a b c Ha Hb Hc Hab Hbc. clear Hb Hc Hab Hbc. cut (a = Empty). intro H. 
  rewrite H. apply subset2_0_all. apply order_eq_0. symmetry. apply le_n_0_eq.
  exact Ha.
  (* n => n+1 *)
  clear n. intros n IH. intros a b c Ha Hb Hc Hab Hbc. apply subset2_elements.
  intros x Hx. cut (exists y:set, In y (elements b) /\ equiv2 x y). 
  intro H. elim H. intros y Hy.
  cut (exists z:set, In z (elements c) /\ equiv2 y z). intro H'. elim H'.
  intros z Hz. exists z. split. elim Hz. auto. unfold equiv2.
  split.

  apply IH with (b:=y). 
  apply le_S_n. apply le_trans with (m:= order a). apply elements_order. exact Hx. 
  exact Ha. 
  apply le_S_n. apply le_trans with (m:=order b). apply elements_order. elim Hy.
  auto. exact Hb.
  apply le_S_n. apply le_trans with (m:= order c). apply elements_order. elim Hz.
  auto. exact Hc.
 
  elim Hy. intros H0 EQxy. clear H0. unfold equiv2 in EQxy. 
  apply proj1 with (B:= subset2 y x). exact EQxy. 

  elim Hz. intros H0 EQyz. clear H0. unfold equiv2 in EQyz. 
  apply proj1 with (B:= subset2 z y). exact EQyz.

  apply IH with (b:=y).
  apply le_S_n. apply le_trans with (m:= order c). apply elements_order. elim Hz.
  auto. exact Hc.
  apply le_S_n. apply le_trans with (m:= order b). apply elements_order. elim Hy.
  auto. exact Hb.
  apply le_S_n. apply le_trans with (m:= order a). apply elements_order. exact Hx.
  exact Ha.
  
  elim Hz. intros H0 EQyz. clear H0. unfold equiv2 in EQyz. 
  apply proj2 with (A:= subset2 y z). exact EQyz.

  elim Hy. intros H0 EQxy. clear H0. unfold equiv2 in EQxy. 
  apply proj2 with (A:= subset2 x y). exact EQxy.
 
  apply subset2_elements with (a:=b). exact Hbc. elim Hy. auto.
  apply subset2_elements with (a:=a). exact Hab. exact Hx.
Qed.






















  
