Set Implicit Arguments.
Require Import Arith.
Require Import Arith.Max.

Definition bool_and (p q:bool) := if p then q else false.
Definition bool_or  (p q:bool) := if p then true else q.

Inductive set : Set := 
  | Empty     : set
  | Singleton : set -> set
  | Union     : set -> set -> set.

Fixpoint order (s:set) : nat :=
  match s with 
    | Empty         => 0
    | Singleton x   => 1 + order x
    | Union x y     => 1 + max (order x) (order y) 
  end.

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

Lemma plus_eq_0_l : forall (n m:nat), n + m = 0 -> n = 0.
Proof.
  intro n. elim n. auto. clear n. intros n IH.
  intro m. simpl. intro H. discriminate H.
Qed.

Lemma plus_eq_0_r : forall (n m:nat), n + m = 0 -> m = 0.
Proof.
  intros. rewrite plus_comm in H. generalize H. apply plus_eq_0_l.
Qed.

Lemma order_eq_0 : forall (a:set), order a = 0 -> a = Empty.
Proof.
  intro a. elim a. auto. clear a. intro a. intro IH. intro H.
  simpl in H. discriminate H. clear a. intro a. intro IH. intro b. intro H.
  intro H'. simpl in H'. discriminate H'.
Qed.

Lemma order_sum_eq_0_l : forall (a b:set),
  order a + order b = 0 -> a = Empty.
Proof.
  intros a b. intro H. apply order_eq_0. apply plus_eq_0_l with (m:= order b).
  exact H.
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

