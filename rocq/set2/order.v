Require Import Arith.
Import Nat.

Require Import set.

(******************************************************************************)
(*                         order : set -> nat                                 *)
(******************************************************************************)

(* The map order : set -> nat is a measure of the 'syntactic complexity' of the
 * expression defining a set. It will be useful as a way to prove many results
 * allowing us to carry induction arguments based on the 'order' of a set.
 *
 * order(0)   = 0
 * order({x}) = 1 + order(x)
 * order(xUy) = 1 + max(order(x), order(y))
 *)

Fixpoint order (s:set) : nat :=
  match s with
    | Empty         => 0
    | Singleton x   => 1 + order x
    | Union x y     => 1 + max (order x) (order y)
  end.

(*  order(a) = 0  =>  a = 0  *)
Lemma order_eq_0 : forall (a:set), order a = 0 -> a = Empty.
Proof.
  intro a. elim a. auto. clear a. intro a. intro IH. intro H.
  simpl in H. discriminate H. clear a. intro a. intro IH. intro b. intro H.
  intro H'. simpl in H'. discriminate H'.
Qed.

(* order(a) + order(b) = 0  =>  a = 0  *)
Lemma order_sum_eq_0_l : forall (a b:set),
  order a + order b = 0 -> a = Empty.
Proof.
  intros a b H. apply order_eq_0.
  apply and_ind with (A:= order a = 0)(B:= order b = 0). trivial.
  apply eq_add_0. exact H.
Qed.

(* order(a) + order(b) = 0 =>  b = 0  *)
Lemma order_sum_eq_0_r : forall (a b:set),
  order a + order b = 0 -> b = Empty.
Proof.
  intros a b H. rewrite add_comm in H. apply order_sum_eq_0_l
  with (b:=a). exact H.
Qed.

(* order({x}) + order(b) <= n+1  =>  order(x) + order(b) <= n  *)
Lemma order_sum_singleton_l : forall (n:nat) (x b:set),
  order (Singleton x) + order b <= S n ->
  order x + order b <= n.
Proof.
  intros n x b H. apply le_S_n. apply le_trans with
  (m:= order (Singleton x) + order b). simpl. apply le_n. exact H.
Qed.

(* order(a) + order({y}) <= n+1  =>  order(a) + order(y) <= n  *)
Lemma order_sum_singleton_r : forall (n:nat) (a y:set),
  order a + order (Singleton y) <= S n ->
  order a + order y <= n.
Proof.
  intros n a y H. rewrite add_comm. apply order_sum_singleton_l.
  rewrite add_comm in H. exact H.
Qed.


(* order({x}) + order({y}) <= n+1  =>  order(x) + order(y) < n *)
Lemma order_sum_singleton_strong : forall (n:nat) (x y:set),
  order (Singleton x) + order (Singleton y) <= S n ->
  order x + order y < n.
Proof.
  intros n x y H. unfold lt. apply le_S_n. apply le_trans with
  (m:= order (Singleton x) + order (Singleton y)). simpl.
  rewrite <- add_succ_r. simpl. reflexivity. exact H.
Qed.

(* This is a weakening of the previous result *)
(* order({x}) + order({y}) <= n+1  => order(x) + order(y) <= n *)
Lemma order_sum_singleton : forall (n:nat) (x y:set),
  order (Singleton x) + order (Singleton y) <= S n ->
  order x + order y <= n.
Proof.
  intros n x y H. apply le_S_n. apply le_S. fold (order x + order y < n).
  apply order_sum_singleton_strong. exact H.
Qed.


(* 'L' refers to where 'Union' stands in the sum
** while 'l' refers to the left argument of Union *)
Lemma order_sum_union_Ll : forall (n:nat) (x y b:set),
  order (Union x y) + order b <= S n ->
  order x + order b <= n.
Proof.
  intros n x y b H. apply le_S_n. apply le_trans with
  (m:= order (Union x y) + order b). simpl. apply le_n_S.
  apply add_le_mono_r. simpl. apply le_max_l. exact H.
Qed.

(* same proof, but use le_max_r instead of le_max_l *)
Lemma order_sum_union_Lr : forall (n:nat) (x y b:set),
  order (Union x y) + order b <= S n ->
  order y + order b <= n.
Proof.
  intros n x y b H. apply le_S_n. apply le_trans with
  (m:= order (Union x y) + order b). simpl. apply le_n_S.
  apply add_le_mono_r. simpl. apply le_max_r. exact H.
Qed.

(* consequence of 'Ll' lemma and commutativity *)
Lemma order_sum_union_Rl : forall (n:nat) (a y z:set),
  order a + order (Union y z) <= S n ->
  order a + order y <= n.
Proof.
  intros n a y z H. rewrite add_comm. apply order_sum_union_Ll
  with(x:= y)(y:=z). rewrite add_comm in H. exact H.
Qed.

(* consequence of 'Lr' lemma and commutativity *)
Lemma order_sum_union_Rr : forall (n:nat) (a y z:set),
  order a + order (Union y z) <= S n ->
  order a + order z <= n.
Proof.
  intros n a y z H. rewrite add_comm. apply order_sum_union_Lr
  with(x:= y)(y:=z). rewrite add_comm in H. exact H.
Qed.


