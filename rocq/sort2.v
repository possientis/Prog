(* deprecated code *)

Fixpoint sort_n (n:nat): list A -> list A :=
  match n with
    | 0   => (fun l =>  l)
    | S p => (fun l =>
      match l with
        | nil       =>  l
        | (x::l')   =>  let m := sort_n p l' in
                        let y':= least l'  in
                        match y' with
                          | None    => l
                          | Some y  => match R_bool x y with
                                        | true  => x::m
                                        | false => y::sort_n p (x::tl m)
                                       end
                        end
      end)
  end.   

Lemma length_sort_n : forall (n:nat)(l:list A),
  length (sort_n n l) = length l.
Proof.
  (* induction on *)
  intro n. elim n.
  (* n = 0 *)
  simpl. reflexivity.
  (* n -> n + 1 *)
  clear n. intros n IH.
  (* induction on l *)
  intro l. elim l.
  (* l = nil *)
  simpl. reflexivity.
  (* l = cons a l *)
  clear l. intros a l H. unfold sort_n. fold sort_n.
  generalize (none_or_not_none (least l)). intro H0. elim H0.
  clear H0. intro H0. rewrite H0. reflexivity.
  clear H0. intro H0. generalize (not_none_is_some (least l)). intro H1.
  rewrite H1 in H0. clear H1. elim H0. clear H0. intros x Hx. rewrite Hx.
  generalize (R_total a x). intro H0. elim H0.
  clear H0. intro H0. rewrite R_lem in H0. rewrite H0. simpl.
  rewrite IH. reflexivity.
  clear H0. intro H0. rewrite R_lem in H0.
  generalize (bool_dec (R_bool a x) true). intro H1. elim H1.
  clear H1. intro H1. rewrite H1. simpl. rewrite IH. reflexivity.
  clear H1. intro H1. apply not_true_is_false in H1. rewrite H1.
  simpl. rewrite IH with (l:= a :: tl (sort_n n l)). simpl. 
  rewrite length_of_tl. rewrite IH. reflexivity. unfold not.
  clear H0 H1. intro H0. rewrite <- length_zero_iff_nil in H0.
  rewrite IH in H0. rewrite length_zero_iff_nil in H0. 
  rewrite <- least_none in H0. rewrite H0 in Hx. discriminate.
Qed.

(* the trick is to control the unfolding process by defining variable n' = S n *)
(* unfolding is needed to move forward and gain visibility. However, too much  *)
(* unfolding makes you utterly blind                                           *) 
Lemma sort_n_Sn : forall (n:nat)(l: list A),
  length l <= n -> sort_n n l = sort_n (S n) l.
Proof.
  (* induction on n *)
  intros n. elim n.
  (* n = 0 *) 
  clear n. intros l H. generalize (nil_or_not_nil l). intro H0. elim H0.
  clear H0. intro H0. rewrite H0. simpl. reflexivity.
  clear H0. intro H0. apply False_ind. apply le_n_0_eq in H.
  symmetry in H. rewrite length_zero_iff_nil in H. apply H0. exact H.
  (* n -> n + 1 *)
  clear n. intros n IH l H. set (n':= S n) (* trick *). unfold sort_n at 1.
  unfold n' at 1. fold sort_n. symmetry. unfold sort_n at 1. fold sort_n.
  generalize H. clear H. elim l.
  intros. reflexivity.
  clear l. intros a l IH'. clear IH'.
  intro H. set (m:= sort_n n' l). unfold m. (* trick *)
  generalize (nil_or_not_nil l). intro Hnil. elim Hnil. clear Hnil. intro Hnil.
  rewrite Hnil. simpl. reflexivity.
  clear Hnil. intro Hnil. unfold n'. rewrite <- IH, <- IH. reflexivity.
  simpl. rewrite length_of_tl. rewrite length_sort_n. simpl in H.
  apply le_S_n. exact H. intro Hnil'. rewrite <- length_zero_iff_nil in Hnil'.
  rewrite length_sort_n in Hnil'. rewrite length_zero_iff_nil in Hnil'.
  apply Hnil. exact Hnil'. simpl in H. apply le_S_n. exact H.
Qed.


(* we are now in a position to define the sort function *)
Definition sort' (l:list A) : list A := sort_n (length l) l.

(* There is one thing we can immediately say about sort *)
Lemma length_sort' : forall (l:list A), length (sort' l) = length l.
Proof.
  intros l. unfold sort'. apply length_sort_n.
Qed.

(*
Lemma In_imp_In_sort_n: forall (n:nat)(l:list A)(x:A),
  In x l -> In x (sort_n n l).
Proof.
  intros n. elim n.
  clear n. simpl. auto.
  clear n. intros n IH l. elim l.
  clear l. auto.
  clear l. intros a l H0 x H1.
  set (L:= least l). cut(L = least l ->  In x (sort_n (S n) (a :: l))). eauto.
  elim L. clear L. intros L H2. set (b1:= R_bool a L). 
  cut(b1 = R_bool a L ->  In x (sort_n (S n) (a :: l))). eauto. elim b1.
  clear b1. intro H3. simpl. rewrite <- H2. rewrite <- H3.
  simpl in H1. elim H1. 
  clear H1. intro H1. simpl. left. exact H1.
  clear H1. intro H1. simpl. right. apply IH. exact H1.
  clear b1. intro H3. simpl. rewrite <- H2. rewrite <- H3.
  simpl in H1. elim H1.
  clear H1. intro H1. simpl. right. apply IH. simpl. left. exact H1.
  clear H1. intro H1.
  generalize (A_dec x L). intro H4. elim H4.
  clear H4. intro H4. simpl. left. symmetry. exact H4.
  clear H4. intro H4. simpl. right. apply IH. right.
(* it is wrong to assume that L is the head of sort_n n when n = 0 *)

*)

(*
Lemma sort_n_Sorted: forall (n:nat)(l:list A),
  length l <= n -> Sorted (sort_n n l).
Proof.
  intros n. elim n.
  clear n. intros l H. apply le_n_0_eq in H. symmetry in H.
  rewrite length_zero_iff_nil in H. rewrite H. simpl. apply SortedNil.
  clear n. intros n IH. intro l. elim l.
  clear l. intro H. clear H. simpl. apply SortedNil.
  clear l. intros a l H0 H1. set (L := least l).
  cut (L = least l -> Sorted (sort_n (S n) (a :: l))). eauto. elim L.
  clear L. intros L H2. set (b1 := R_bool a L).
  cut (b1 = R_bool a L -> Sorted (sort_n (S n) (a :: l))). eauto. elim b1.
  clear b1. intros H3. unfold sort_n. fold sort_n. 
  rewrite <- H2. rewrite <- H3. apply SortedCons. apply smallest_imp_Least.
  simpl. left. reflexivity. intros b H4. simpl in H4. elim H4.
  clear H4. intro H4. rewrite H4. apply R_refl.
  (* sort_n n l and l have the same elements ? *)

*)

(*
(* now that we formally know what a sorted list is, we can state *)
Theorem sort_l_Sorted: forall (l:list A), Sorted (sort l).
Proof.
*)




