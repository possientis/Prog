Require Import Arith.
Require Import Arith.Max.

Require Import set.
Require Import order.

(******************************************************************************)
(*                       subset : set -> set -> Prop                          *)
(******************************************************************************)
(*
  We have defined a type 'set' which is meant to represent a subclass of the 
  set theoretic class of finite sets.

  TODO
*)

Fixpoint subset_n (n:nat) : set -> set -> Prop :=
  match n with 
    | 0   => (fun _ _     => True)
    | S p => (fun a b     =>
      match a with
        | Empty           => True
        | Singleton x     => 
          match b with
            | Empty       => False
            | Singleton y => subset_n p x y /\ subset_n p y x
            | Union y z   => subset_n p (Singleton x) y \/
                             subset_n p (Singleton x) z 
          end
        | Union x y       => subset_n p x b /\ subset_n p y b
      end)
  end.

Lemma subset_n_Sn : forall (n:nat) (a b:set),
  order a + order b <= n -> (subset_n n a b <-> subset_n (S n) a b).
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
  unfold subset_n at 1. fold subset_n.
  cut(subset_n (S (S n)) (Singleton x) (Singleton y) <-> 
     (subset_n (S n) x y)/\(subset_n (S n) y x)). 
  intro H'. rewrite H'. rewrite <- IH, <- IH. tauto.
  apply order_sum_singleton. rewrite plus_comm. exact H.
  apply order_sum_singleton. exact H.
  simpl. reflexivity.
  (* b = Union y z *)
  clear b. intros y Hy z Hz H.
  unfold subset_n at 1. fold subset_n.
  cut(subset_n (S (S n)) (Singleton x) (Union y z) <->
     (subset_n (S n) (Singleton x) y)\/(subset_n (S n) (Singleton x) z)).
  intro H'. rewrite H'. rewrite <- IH, <- IH. tauto.
  apply order_sum_union_Rr with (y:=y). exact H.
  apply order_sum_union_Rl with (z:=z). exact H. 
  simpl. reflexivity.
  (* a = Union x y *)
  clear a. intros x Hx y Hy b H.
  unfold subset_n at 1. fold subset_n.
  cut(subset_n (S (S n)) (Union x y) b <-> 
     (subset_n (S n) x b)/\(subset_n (S n) y b)).
  intro H'. rewrite H'. rewrite <- IH, <- IH. tauto.
  apply order_sum_union_Lr with (x:=x). exact H.
  apply order_sum_union_Ll with (y:=y). exact H.
  simpl. reflexivity.
  Qed.

Definition subset (a b:set) : Prop :=
  let n:= order a + order b in subset_n n a b.

Lemma subset_subset_n : forall (n:nat) (a b:set),
  order a + order b <= n -> (subset a b <-> subset_n n a b).
Proof.
  (* induction on n *)
  intros n. elim n.
  (* n = 0 *)
  intros a b H. cut (a = Empty). cut (b = Empty). intros Hb Ha. rewrite Ha, Hb.
  unfold subset. simpl. tauto.
  apply order_sum_eq_0_r with (a:=a). symmetry. apply le_n_0_eq. exact H.
  apply order_sum_eq_0_l with (b:=b). symmetry. apply le_n_0_eq. exact H.
  (* n -> n+1 *)
  clear n. intros n IH a b H.
  (* either order a + order b < S n or = S n *)
  cut((order a + order b < S n)\/(order a + order b = S n)). intro H0. elim H0.
  (* order a + order b < S n *)
  intro H1. rewrite IH. apply subset_n_Sn. 
  apply le_S_n. exact H1. apply le_S_n. exact H1. 
  (* order a + order b = S n *)
  intro H1. unfold subset. rewrite H1. tauto.
  (* finally *)
  apply le_lt_or_eq. exact H.
Qed.

Lemma subset_0_all : forall (b:set), subset Empty b.
Proof.
  (* induction on b *)
  intro b. elim b.
  (* b = Empty *)
  unfold subset. simpl. apply I.
  (* b = Singleton x *)
  clear b. intros x H. unfold subset. simpl. apply I.
  (* b = Union x y *)
  clear b. intros x Hx y Hy. unfold subset. simpl. apply I.
Qed.

Lemma subset_single_0 : forall (x:set), ~subset (Singleton x) Empty.
Proof.
  (* not structural induction necessary *)
  intro x. unfold subset. simpl. tauto.
Qed.


Lemma subset_single_single : forall (x y:set),
  subset (Singleton x) (Singleton y) <-> (subset x y)/\(subset y x).
Proof.
  intros x y. unfold subset at 1. simpl. 
  rewrite <- subset_subset_n, <- subset_subset_n. tauto.
  rewrite plus_comm. apply plus_le_compat_l. apply le_S. apply le_n.
  apply plus_le_compat_l. apply le_S. apply le_n.
Qed.

Lemma subset_single_union: forall (x y z:set),
  subset (Singleton x) (Union y z) <-> 
  (subset (Singleton x) y)\/(subset (Singleton x) z).
Proof.
  intros x y z. unfold subset at 1. simpl.
  rewrite <- subset_subset_n, <- subset_subset_n. tauto. 
  simpl. rewrite <- plus_n_Sm. apply le_n_S. 
  apply plus_le_compat_l. apply le_max_r.
  simpl. rewrite <- plus_n_Sm. apply le_n_S. 
  apply plus_le_compat_l. apply le_max_l.
Qed.

Lemma subset_union_all : forall (x y b:set),
  subset (Union x y) b <-> (subset x b)/\(subset y b).
Proof.
  intros x y b. unfold subset at 1. simpl.
  rewrite <- subset_subset_n, <- subset_subset_n. tauto.
  apply plus_le_compat_r. apply le_max_r. apply plus_le_compat_r. apply le_max_l.
Qed.

Definition subset_prop_1 (relation: set -> set -> Prop) : Prop :=
  forall (b:set), relation Empty b.

Definition subset_prop_2 (relation: set -> set -> Prop) : Prop :=
  forall (x:set), ~relation (Singleton x) Empty.

Definition subset_prop_3 (relation: set-> set -> Prop) : Prop :=
  forall (x y:set),
  relation (Singleton x) (Singleton y) <-> relation x y /\ relation y x.

Definition subset_prop_4 (relation: set -> set -> Prop) : Prop :=
  forall (x y z:set),
  relation (Singleton x) (Union y z) <->
  relation (Singleton x) y \/ relation (Singleton x) z.

Definition subset_prop_5 (relation: set -> set -> Prop) : Prop :=
  forall (x y b:set),
  relation (Union x y) b <-> relation x b /\ relation y b.

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
Lemma subset_unique : forall (relation : set -> set -> Prop),
  subset_prop_1 relation ->
  subset_prop_2 relation ->
  subset_prop_3 relation ->
  subset_prop_4 relation ->
  subset_prop_5 relation ->
  forall (a b:set), relation a b <-> subset a b.
Proof.
  intros relation H1 H2 H3 H4 H5 a b.
  (* proof by induction on order a + order b <= n *)
  cut(forall n:nat, order a + order b <= n -> (relation a b <-> subset a b)).
  intro H. apply H with (n:= order a + order b). apply le_n.
  intro n. generalize a b. clear a b. elim n.
  (* order a + order b <= 0 *) 
  intros a b H. cut (a = Empty). intro H'. rewrite H'.
  split. intros. apply subset_0_all. intros. apply H1.
  apply order_sum_eq_0_l with (b:=b). symmetry. apply le_n_0_eq. exact H.
  (* true for <= n -> true for <= n+1 *)
  (* induction on a *)  
  clear n. intros n IH a. elim a.
  (* a = Empty *)
  intros b H. split. intros. apply subset_0_all. intros. apply H1.
  (* a = Singleton x *)(* induction on b *)
  clear a. intros x H b. elim b.
  (* b = Empty *)
  intros. split. 
  intros. apply False_ind. apply H2 with (x:=x). exact H6.
  intros. apply False_ind. apply subset_single_0 with (x:=x). exact H6. 
  (* b = Singleton y *)
  clear b. intros y H' H''. unfold subset_prop_3 in H3. 
  rewrite H3, subset_single_single, IH, IH. tauto.
  rewrite plus_comm. apply order_sum_singleton. exact H''.
  apply order_sum_singleton. exact H''.
  (* b = Union y z *)
  clear b. intros y Hy z Hz H'. unfold subset_prop_4 in H4.
  rewrite H4, subset_single_union, IH, IH. tauto.
  apply order_sum_union_Rr with (y:=y). exact H'.
  apply order_sum_union_Rl with (z:=z). exact H'.
  (* a = Union x y *)
  clear a. intros x Hx y Hy b H. unfold subset_prop_5 in H5.
  rewrite H5, subset_union_all, IH, IH. tauto.
  apply order_sum_union_Lr with (x:=x). exact H.
  apply order_sum_union_Ll with (y:=y). exact H.
Qed.



