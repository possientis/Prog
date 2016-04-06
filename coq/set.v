Set Implicit Arguments.
Require Import Arith.

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

Definition bool_and (p q:bool) := if p then q else false.
Definition bool_or  (p q:bool) := if p then true else q.

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

Lemma subset_n_0_b : forall (n:nat) (b:set), subset_n n Empty b = true.
Proof.
  intro n. elim n. intro b. simpl. trivial. clear n. intro n.
  intro IH. intro b. simpl. trivial.
Qed.

Lemma subset_n_sx_0 : forall (n:nat) (x:set), 
  (1 <= n) -> subset_n n (Singleton x) Empty = false.
Proof.
  intro n. elim n. intros x H. simpl. cut (0 = 1). intro H'.
  discriminate H'. apply le_n_0_eq. exact H. clear n. intro n.
  intro IH. intro x. intro H. simpl. trivial. 
Qed.

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


Lemma order_sum_singleton : forall (n:nat) (x y:set),
  order (Singleton x) + order (Singleton y) <= S n ->
  order x + order y <= n.
Proof.
  intros n x y H. apply le_S_n. apply le_trans with 
  (m:= order (Singleton x) + order (Singleton y)). simpl. apply le_n_S.
  apply plus_le_compat_l. apply le_n_Sn. exact H. 
Qed.

Lemma order_sum_singleton_l : forall (n:nat) (x b:set),
  order (Singleton x) + order b <= S n ->
  order x + order b <= n.
Proof.
  intros n x b H. apply le_S_n. apply le_trans with
  (m:= order (Singleton x) + order b). simpl. apply le_n. exact H.
Qed.

Lemma order_sum_singleton_r : forall (n:nat) (a y:set),
  order a + order (Singleton y) <= S n ->
  order a + order y <= n.
Proof. 
  intros n a y H. apply le_S_n. apply le_trans with 
  (m:= order a + order (Singleton y)). simpl.
  rewrite <- plus_n_Sm. reflexivity. exact H.
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
  apply IH. 
  
 (* 
  apply order_sum_singleton. rewrite plus_comm. exact H.
  apply IH. apply order_sum_singleton. exact H. simpl. reflexivity.
  simpl. reflexivity. clear b. intros y Hy z Hz H. clear Hy Hz. 
  cut(subset_n (S n) (Singleton x) (Union y z) =
  bool_or (subset_n n (Singleton x) y) (subset_n n (Singleton x) z)).  
  cut(subset_n (S (S n)) (Singleton x) (Union y z) =
  bool_or (subset_n (S n) (Singleton x) y) (subset_n (S n) (Singleton x) z)).
  intros H1 H2. rewrite H1.
  cut(subset_n n (Singleton x) y = subset_n (S n) (Singleton x) y).
  cut(subset_n n (Singleton x) z = subset_n (S n) (Singleton x) z).
  intros H3 H4. rewrite <- H3, <- H4, H2. reflexivity.
  apply IH.
  *)

