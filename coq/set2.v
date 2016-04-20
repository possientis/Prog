Require Import set.
Require Import Bool.
Require Import Arith.

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

Lemma subset_bool_prop : forall (n:nat)(a b:set),
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
  intro H'. rewrite H'. rewrite <- IH. rewrite <- IH. tauto.
  apply order_sum_singleton. rewrite plus_comm. exact H.
  apply order_sum_singleton. exact H.
  unfold subset2_n. reflexivity.


