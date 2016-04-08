Set Implicit Arguments.
Require Import Arith.
Require Import Arith.Max.

Definition bool_and (p q:bool) := if p then q else false.
Definition bool_or  (p q:bool) := if p then true else q.

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

Lemma subset_none_0 : forall (x:set), subset (Singleton x) Empty = false.
Proof.
  intro x. unfold subset. simpl. reflexivity. (* no structural induction  *)
Qed.


Lemma subset_singletons : forall (x y:set), 
  subset (Singleton x) (Singleton y) = bool_and (subset x y) (subset y x). 
Proof.
  intros x y. unfold subset at 1. simpl.
  cut(subset_n (order x + S (order y)) x y = subset x y).
  cut(subset_n (order x + S (order y)) y x = subset y x).
  intros H0 H1. rewrite H0, H1. reflexivity. symmetry. apply subset_subset_n. 
  rewrite plus_comm. apply plus_le_compat_l. apply le_S. apply le_n.
  symmetry. apply subset_subset_n. apply plus_le_compat_l. apply le_S. apply le_n.
Qed.

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








