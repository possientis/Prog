Set Implicit Arguments.
Require Import Arith.
Require Import Arith.Max.
Require Import List.

Definition bool_and (p q:bool) :=
  match p, q with
    | true, true    => true
    | true, false   => false
    | false, true   => false
    | false, false  => false
  end.

Definition bool_or (p q:bool) :=
  match p, q with
    | true, true    => true
    | true, false   => true
    | false, true   => true
    | false, false  => false
  end.

Lemma lemma_or_true : forall (p q:bool), 
  bool_or p q = true -> p = true \/ q = true.
Proof.
  intro p. elim p; intro q; elim q; simpl; auto.
Qed.


Inductive set : Set := 
  | Empty     : set
  | Singleton : set -> set
  | Union     : set -> set -> set.

(******************************************************************************)
(*                         order : set -> nat                                 *)
(******************************************************************************)

Fixpoint order (s:set) : nat :=
  match s with 
    | Empty         => 0
    | Singleton x   => 1 + order x
    | Union x y     => 1 + max (order x) (order y) 
  end.
 
Lemma order_eq_0 : forall (a:set), order a = 0 -> a = Empty.
Proof.
  intro a. elim a. auto. clear a. intro a. intro IH. intro H.
  simpl in H. discriminate H. clear a. intro a. intro IH. intro b. intro H.
  intro H'. simpl in H'. discriminate H'.
Qed.

Lemma order_sum_eq_0_l : forall (a b:set),
  order a + order b = 0 -> a = Empty.
Proof.
  intros a b H. apply order_eq_0. 
  apply and_ind with (A:= order a = 0)(B:= order b = 0). trivial.
  apply plus_is_O. exact H.
Qed.

(* immediate consequence of previous lemma and commutativity *)
Lemma order_sum_eq_0_r : forall (a b:set),
  order a + order b = 0 -> b = Empty.
Proof.
  intros a b H. rewrite plus_comm in H. apply order_sum_eq_0_l
  with (b:=a). exact H.
Qed.

(* This is the main proof of the order_sum_singleton lemmas *)
Lemma order_sum_singleton_l : forall (n:nat) (x b:set),
  order (Singleton x) + order b <= S n ->
  order x + order b <= n.
Proof.
  intros n x b H. apply le_S_n. apply le_trans with
  (m:= order (Singleton x) + order b). simpl. apply le_n. exact H.
Qed.

(* simply use commutativity of addition and apply previous lemma *)
Lemma order_sum_singleton_r : forall (n:nat) (a y:set),
  order a + order (Singleton y) <= S n ->
  order a + order y <= n.
Proof. 
  intros n a y H. rewrite plus_comm. apply order_sum_singleton_l.
  rewrite plus_comm in H. exact H.
Qed.

(* simply use commutativity of addition and apply 'left' version *)
Lemma order_sum_singleton : forall (n:nat) (x y:set),
  order (Singleton x) + order (Singleton y) <= S n ->
  order x + order y <= n.
Proof.
  intros n x y H. apply order_sum_singleton_l. rewrite plus_comm.
  apply order_sum_singleton_l. rewrite plus_comm. apply le_S. exact H.
Qed.

(* 'L' refers to where 'Union' stands in the sum
** while 'l' refers to the left argument of Union *)
Lemma order_sum_union_Ll : forall (n:nat) (x y b:set),
  order (Union x y) + order b <= S n ->
  order x + order b <= n.
Proof.
  intros n x y b H. apply le_S_n. apply le_trans with
  (m:= order (Union x y) + order b). simpl. apply le_n_S.
  apply plus_le_compat_r. simpl. apply le_max_l. exact H.
Qed.
  
(* same proof, but use le_max_r instead of le_max_l *)
Lemma order_sum_union_Lr : forall (n:nat) (x y b:set),
  order (Union x y) + order b <= S n ->
  order y + order b <= n.
Proof.
  intros n x y b H. apply le_S_n. apply le_trans with
  (m:= order (Union x y) + order b). simpl. apply le_n_S.
  apply plus_le_compat_r. simpl. apply le_max_r. exact H.
Qed.

(* consequence of 'Ll' lemma and commutativity *)
Lemma order_sum_union_Rl : forall (n:nat) (a y z:set),
  order a + order (Union y z) <= S n ->
  order a + order y <= n.
Proof.
  intros n a y z H. rewrite plus_comm. apply order_sum_union_Ll
  with(x:= y)(y:=z). rewrite plus_comm in H. exact H.
Qed.

(* consequence of 'Lr' lemma and commutativity *)
Lemma order_sum_union_Rr : forall (n:nat) (a y z:set),
  order a + order (Union y z) <= S n ->
  order a + order z <= n.
Proof.
  intros n a y z H. rewrite plus_comm. apply order_sum_union_Lr
  with(x:= y)(y:=z). rewrite plus_comm in H. exact H.
Qed.

(******************************************************************************)
(*                       subset : set -> set -> bool                          *)
(******************************************************************************)

Fixpoint subset_n (n:nat) : set -> set -> bool :=
  match n with 
    | 0   => (fun _ _     => true)
    | S p => (fun a b     =>
      match a with
        | Empty           => true
        | Singleton x     => 
          match b with
            | Empty       => false
            | Singleton y => bool_and (subset_n p x y) (subset_n p y x)
            | Union y z   => bool_or  (subset_n p (Singleton x) y)
                                      (subset_n p (Singleton x) z) 
          end
        | Union x y       => bool_and (subset_n p x b) (subset_n p y b)
      end)
  end.

Lemma subset_n_Sn : forall (n:nat) (a b:set),
  order a + order b <= n -> subset_n n a b = subset_n (S n) a b.
Proof.
  intro n. elim n. intros a b. intro H. cut (a = Empty). intro H'. 
  rewrite H'. simpl. trivial. apply order_sum_eq_0_l with (b:=b).
  cut (0 = order a + order b). intro H'. rewrite <- H'. trivial.
  apply le_n_0_eq. exact H. clear n. intros n IH a b. elim a. 
  intro H. simpl. trivial. clear a. intros x Hx. clear Hx.
  elim b. intro H. simpl. trivial. intros y Hy H. clear Hy. 
  cut (subset_n (S n) (Singleton x) (Singleton y) = 
  bool_and (subset_n n x y) (subset_n n y x)).
  cut (subset_n (S (S n)) (Singleton x) (Singleton y) =
  bool_and (subset_n (S n) x y) (subset_n (S n) y x)).
  intros H1 H2. rewrite H1.
  cut (subset_n n x y = subset_n (S n) x y).
  cut (subset_n n y x = subset_n (S n) y x).
  intros H3 H4. rewrite <- H3, <- H4, H2. reflexivity.
  apply IH. apply order_sum_singleton. rewrite plus_comm. exact H.
  apply IH. apply order_sum_singleton. exact H. 
  simpl. reflexivity. simpl. reflexivity. 
  clear b. intros y Hy z Hz H. clear Hy Hz. 
  cut(subset_n (S n) (Singleton x) (Union y z) =
  bool_or (subset_n n (Singleton x) y) (subset_n n (Singleton x) z)).  
  cut(subset_n (S (S n)) (Singleton x) (Union y z) =
  bool_or (subset_n (S n) (Singleton x) y) (subset_n (S n) (Singleton x) z)).
  intros H1 H2. rewrite H1.
  cut(subset_n n (Singleton x) y = subset_n (S n) (Singleton x) y).
  cut(subset_n n (Singleton x) z = subset_n (S n) (Singleton x) z).
  intros H3 H4. rewrite <- H3, <- H4, H2. reflexivity.
  apply IH. apply order_sum_union_Rr with (y:= y). exact H.
  apply IH. apply order_sum_union_Rl with (z:= z). exact H.
  simpl. reflexivity. simpl. reflexivity.
  intros x Hx. clear Hx. intros y Hy. clear Hy. intro H.
  cut(subset_n (S (S n)) (Union x y) b = 
  bool_and (subset_n (S n) x b) (subset_n (S n) y b)).
  intro H'. rewrite H'.
  cut(subset_n n x b = subset_n (S n) x b).
  cut(subset_n n y b = subset_n (S n) y b).
  intros H1 H2. rewrite <- H1, <- H2. simpl. reflexivity.
  apply IH. apply order_sum_union_Lr with (x:=x). exact H.
  apply IH. apply order_sum_union_Ll with (y:=y). exact H.
  simpl. reflexivity.
Qed.

Definition subset (a b:set) : bool :=
  let n := order a + order b in subset_n n a b.

Lemma subset_subset_n : forall (n:nat) (a b:set),
  order a + order b <= n ->  subset a b = subset_n n a b.
Proof.
  intros n a b. unfold subset. elim n. intro H. cut (a = Empty). cut (b = Empty). 
  intros Ha Hb. rewrite Ha, Hb. simpl. reflexivity. 
  apply order_sum_eq_0_r with (a:=a). symmetry. apply le_n_O_eq. exact H.
  apply order_sum_eq_0_l with (b:=b). symmetry. apply le_n_O_eq. exact H.
  clear n. intros n IH H. 
  cut((order a + order b < S n)\/(order a + order b = S n)). intro H0. elim H0.
  intro H1. cut(order a + order b <= n). intro H2. rewrite IH. apply subset_n_Sn.
  exact H2. exact H2. apply lt_n_Sm_le. exact H1. intro H1. rewrite H1. 
  reflexivity. apply le_lt_or_eq. exact H.
Qed.

Lemma subset_0_all : forall (b:set), subset Empty b = true.
Proof.
  intro b. elim b. unfold subset. simpl. reflexivity. 
  clear b. intros b H. clear H. unfold subset. simpl. reflexivity.
  clear b. intros y H1 z H2. clear H1 H2. unfold subset. simpl. reflexivity. 
Qed.

Lemma subset_single_0 : forall (x:set), subset (Singleton x) Empty = false.
Proof.
  intro x. unfold subset. simpl. reflexivity. (* no structural induction  *)
Qed.


Lemma subset_single_single : forall (x y:set), 
  subset (Singleton x) (Singleton y) = bool_and (subset x y) (subset y x). 
Proof.
  intros x y. unfold subset at 1. simpl.
  cut(subset_n (order x + S (order y)) x y = subset x y).
  cut(subset_n (order x + S (order y)) y x = subset y x).
  intros H0 H1. rewrite H0, H1. reflexivity. symmetry. apply subset_subset_n. 
  rewrite plus_comm. apply plus_le_compat_l. apply le_S. apply le_n.
  symmetry. apply subset_subset_n. apply plus_le_compat_l. apply le_S. apply le_n.
Qed.

Lemma subset_single_union : forall (x y z:set),
  subset (Singleton x) (Union y z) = 
  bool_or (subset (Singleton x) y) (subset (Singleton x) z).
Proof.
  intros x y z. unfold subset at 1. simpl. 
  cut(subset_n (order x + S (max (order y) (order z))) (Singleton x) y 
  = subset (Singleton x) y). 
  cut(subset_n (order x + S (max (order y) (order z))) (Singleton x) z = 
  subset (Singleton x) z). 
  intros H0 H1. rewrite H0, H1. reflexivity. 
  symmetry. apply subset_subset_n. simpl. rewrite <- plus_n_Sm. apply le_n_S. 
  apply plus_le_compat_l. apply le_max_r.
  symmetry. apply subset_subset_n. simpl. rewrite <- plus_n_Sm. apply le_n_S. 
  apply plus_le_compat_l. apply le_max_l.
Qed.

Lemma subset_union_all : forall (x y b:set),
  subset (Union x y) b = bool_and (subset x b) (subset y b).
Proof.
  intros x y b. unfold subset at 1. simpl.
  cut(subset_n (max (order x) (order y) + order b) x b = subset x b).
  cut(subset_n (max (order x) (order y) + order b) y b = subset y b).
  intros H0 H1. rewrite H0, H1. reflexivity.
  symmetry. apply subset_subset_n. apply plus_le_compat_r. apply le_max_r.
  symmetry. apply subset_subset_n. apply plus_le_compat_r. apply le_max_l.
Qed.

Definition subset_prop_1 (relation: set -> set -> bool) : Prop :=
  forall (b:set), relation Empty b = true.

Definition subset_prop_2 (relation: set -> set -> bool) : Prop :=
  forall (x:set), relation (Singleton x) Empty = false.

Definition subset_prop_3 (relation: set -> set -> bool) : Prop :=
  forall (x y:set), 
  relation (Singleton x) (Singleton y) = bool_and (relation x y) (relation y x).

Definition subset_prop_4 (relation: set -> set -> bool) : Prop :=
  forall (x y z:set),
  relation (Singleton x) (Union y z) = 
  bool_or (relation (Singleton x) y) (relation (Singleton x) z).

Definition subset_prop_5 (relation: set -> set -> bool) : Prop :=
  forall (x y b:set),
  relation (Union x y) b = bool_and (relation x b) (relation y b).

(* subset is a relation on set satisfying properties 1-5 *)
Lemma subset_exist : 
  subset_prop_1 subset /\
  subset_prop_2 subset /\
  subset_prop_3 subset /\
  subset_prop_4 subset /\
  subset_prop_5 subset.
Proof.
  split. unfold subset_prop_1. apply subset_0_all.
  split. unfold subset_prop_2. apply subset_single_0.
  split. unfold subset_prop_3. apply subset_single_single.
  split. unfold subset_prop_4. apply subset_single_union.
  unfold subset_prop_5. apply subset_union_all.
Qed.

(* subset is the unique relation on set satisfying properties 1-5 *)
Lemma subset_unique : forall (relation: set-> set-> bool),
  subset_prop_1 relation ->
  subset_prop_2 relation ->
  subset_prop_3 relation ->
  subset_prop_4 relation ->
  subset_prop_5 relation ->
  forall (a b:set), relation a b = subset a b.
Proof.
  intros relation H1 H2 H3 H4 H5 a b. 
  cut(forall (n:nat), order a + order b <= n -> relation a b = subset a b).
  intro H. apply H with (n:= order a + order b). apply le_n. intro n.
  generalize a b. clear a b. elim n. intros a b H. cut(a = Empty). intro H'.
  rewrite H'. rewrite subset_0_all. apply H1. apply order_sum_eq_0_l with (b:=b).
  symmetry. apply le_n_0_eq. exact H. clear n. intros n IH a. elim a. intros b H.
  clear H. rewrite subset_0_all. apply H1. clear a. intros x H. clear H. intro b.
  elim b. intro H. clear H. rewrite subset_single_0. apply H2. clear b. intro y.
  intro H. clear H. intro H. rewrite subset_single_single. rewrite H3.
  cut(relation x y = subset x y). cut(relation y x = subset y x). intros Hyx Hxy.
  rewrite Hyx, Hxy. reflexivity. apply IH. apply order_sum_singleton.
  rewrite plus_comm. exact H. apply IH. apply order_sum_singleton. exact H.
  clear b. intros y H z H'. clear H H'. intro H. rewrite subset_single_union.
  rewrite H4. cut(relation (Singleton x) y = subset (Singleton x) y).
  cut(relation (Singleton x) z = subset (Singleton x) z). intros Hxz Hxy.
  rewrite Hxz, Hxy. reflexivity. apply IH. apply order_sum_union_Rr with (y:=y).
  exact H. apply IH. apply order_sum_union_Rl with (z:=z). exact H. intros x H y H'.
  clear H H'. intro b. intro H. rewrite subset_union_all. rewrite H5. 
  cut(relation x b = subset x b). cut(relation y b = subset y b). intros Hyb Hxb. 
  rewrite Hyb, Hxb. reflexivity. apply IH. apply order_sum_union_Lr with (x:=x).
  exact H. apply IH. apply order_sum_union_Ll with (y:=y). exact H.
Qed.

(******************************************************************************)
(*                        equiv : set -> set -> bool                          *)
(******************************************************************************)

Definition equiv (a b:set) : bool := bool_and (subset a b) (subset b a).


(******************************************************************************)
(*                        elements : set -> list set                          *)
(******************************************************************************)

Fixpoint elements (a:set) : list set :=
  match a with
    | Empty         => nil
    | Singleton x   => x::nil
    | Union x y     => (elements x) ++ (elements y) 
  end.

Lemma subset_elements : forall (a b:set), subset a b = true <-> 
  forall (c:set), In c (elements a) -> exists (c':set), 
    In c' (elements b) /\  equiv c c' = true.  
Proof.
  intro a. elim a. intros b. split. intros H c. clear H. simpl. apply False_ind.
  intro H. clear H. apply subset_0_all. clear a. intro x. intro IH. clear IH.
  intro b. elim b. rewrite subset_single_0. split. intro H. discriminate H. 
  intro H. cut(exists c':set, In c' (elements Empty) /\ equiv x c' = true). 
  intro H'. simpl in H'. cut False. apply False_ind. elim H'.
  intro z. intro H''. elim H''. trivial. apply H. simpl. left. reflexivity.
  clear b. intros y H. clear H. simpl. rewrite subset_single_single. split.
  intro H. intros c H'. exists y. split. left. reflexivity. elim H'. intro H''.
  rewrite <- H''. unfold equiv. exact H. apply False_ind. intro H.
  cut(exists c' : set, (y = c' \/ False) /\ equiv x c' = true). intro H'.
  elim H'. intro z. intro H''. elim H''. intros H0 H1. elim H0. intro H2.
  rewrite <- H2 in H1. exact H1. apply False_ind. apply H. left. reflexivity.
  clear b. intros y Hy z Hz. rewrite subset_single_union. simpl. split.
  intros H c H'. elim H'. intro H''. rewrite <- H''. clear H''.
  cut(subset (Singleton x) y = true \/ subset (Singleton x) z = true).
  intro H''. elim H''. intro Hy'. 
  cut(exists c':set, In c' (elements y) /\ equiv x c' = true). intro Hy''.
  elim Hy''. intro c'. intro Hc'. exists c'. split. elim Hc'. intro Hc''.
  intro H0. clear H0. apply in_or_app. left. exact Hc''. elim Hc'. intros H0 H1. 
  exact H1. apply Hy. exact Hy'. simpl. left. reflexivity. intro Hz'.
  cut(exists c':set, In c' (elements z) /\ equiv x c' = true). intro Hz''.
  elim Hz''. intro c'. intro Hc'. exists c'. split. elim Hc'. intro Hc''. intro H0.
  clear H0. apply in_or_app. right. exact Hc''. elim Hc'. intros H0 H1. exact H1.
  apply Hz. exact Hz'. simpl. left. reflexivity. apply lemma_or_true. exact H.
  apply False_ind. intro H.
  cut(exists c' : set, In c' (elements y ++ elements z) /\ equiv x c' = true).
  intro H'.






(*
Definition successor (s:set) : set :=
  Union s (Singleton s).

Fixpoint embed (n:nat) : set :=
  match n with
    | 0   => Empty
    | S p => successor (embed p)
  end.

Definition zero   := embed 0.
Definition one    := embed 1.
Definition two    := embed 2.
Definition three  := embed 3.
Definition four   := embed 4.
Definition five   := embed 5.
Definition six    := embed 6.
Definition seven  := embed 7.
Definition eight  := embed 8.
Definition nine   := embed 9.
Definition ten    := embed 10.
Definition eleven := embed 11.
Definition twelve := embed 12.  
*)








