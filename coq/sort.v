Require Import List.
Require Import Arith.

Parameter A:Type.
Parameter R: A -> A -> Prop.
Parameter R_bool: A -> A -> bool.
Axiom R_refl:   forall x:A, R x x.
Axiom R_anti:   forall x y:A, R x y -> R y x -> x = y.
Axiom R_trans:  forall x y z:A, R x y -> R y z -> R x z.
Axiom R_total:  forall x y:A, R x y \/ R y x.
Axiom R_lem:    forall x y:A, R x y <-> R_bool x y = true.


(* This lemma is part of the Coq 8.5 library *)
Lemma length_zero_iff_nil : forall (A:Type) (l:list A),
  length l = 0 <-> l = nil.
Proof.
  intros A l. elim l. unfold length. split; auto. 
  clear l. intros a l H. split. clear H. simpl. intro H.
  discriminate H. clear H. intro H. discriminate H.
Qed.

Lemma length_of_tl : forall (A:Type) (l: list A),
  l <> nil -> S (length (tl l)) = length l.
Proof.
  intros A l. elim l. unfold not. intro H. apply False_ind. auto.
  clear l. intros a l IH. intro H. clear H. simpl. reflexivity.
Qed.

Fixpoint least (l:list A) : option A :=
  match l with
    | nil     =>  None
    | (x::l') =>  let y' := least l' in
                  match y' with
                    | None    => Some x
                    | Some y  => match R_bool x y with
                                  | true  =>  Some x
                                  | false =>  Some y
                                 end
                  end  
  end.

Lemma least_none : forall (l:list A),
  least l = None <-> l = nil.
Proof.
  intro l. split. elim l. intro H. auto. clear l. intros a l.
  intros H H'. apply False_ind. simpl in H'. set (n:= least l) in H'.
  generalize H'. case n. intro b. set (v:= R_bool a b). case v.
  intro H0. discriminate H0. intro H0. discriminate H0.
  intro H0. discriminate H0.
  intro H. rewrite H. simpl. reflexivity.
Qed.

Lemma least_is_least: forall (l:list A) (a: A),
  least l = Some a <-> In a l /\ 
  forall (b:A), In b l -> R a b. 
Proof. 
  intros l a. split. generalize a. clear a. elim l. 
  intros. simpl in H. discriminate H. clear l.
  intros a l IH b H. split. simpl in H. generalize H.
  clear H. set (ll:= least l). fold ll in IH. generalize IH.
  clear IH. case ll. intros c IH. set (b0:=R_bool a c).
  case b0. intro H. pose (g:= (fun o => match o with | None => a | Some x => x end)).
  fold (g (Some b)). rewrite <- H. simpl. left. reflexivity.
  intro H. elim (IH b). intros. simpl. right. exact H0. exact H.
  intros. pose (g:= (fun o => match o with | None => a | Some x => x end)).
  fold (g (Some a)). rewrite H. simpl. left. reflexivity.
  intro c.




(*
Fixpoint sort_n (n:nat): list A -> list A :=
  match n with
    | 0   => (fun l =>  l)
    | S p => (fun l =>
      match l with
        | nil       =>  l
        | (x::l')   =>  let m := sort_n p l' in
                        let y':= hd_error m  in
                        match y' with
                          | None    => l
                          | Some y  => match R_bool x y with
                                        | true  => x::m
                                        | false => y::sort_n p (x::tl m)
                                       end
                        end
      end)
  end.   
*)








(*
Fixpoint sort_n (n:nat): list A -> list A :=
  match n with
    | 0   => (fun _ => nil)
    | S p => (fun l =>
      match l with
        | nil       =>  nil
        | (x::nil)  =>  (x::nil)
        | (x::l')   =>  let m := sort_n p l' in
                        let y := hd_error m  in
                        match y with
                          | None    => nil (* should not happen *)
                          | Some z  => match R_bool x z with
                                        | true  =>  (x::m)
                                        | false =>  let m' := tl m in
                                                    z::sort_n p (x::m') 
                                       end
                        end
      end)
  end. 


Lemma le_length_sort_n_n : forall (n:nat)(l: list A),
  length (sort_n n l) <= n.
Proof.
  intro n. elim n. auto. clear n. intros n IH l. elim l.
  simpl. auto with arith. clear l. intros a l H. clear H.
  elim l. simpl. auto with arith. clear l. intros b l H.
  clear H. simpl. set (y:= hd_error (sort_n n (b :: l))).
  case y. intro c. set (comp := R_bool a c). case comp.
  simpl. apply le_n_S. apply IH. simpl. apply le_n_S.
  apply IH. simpl. auto with arith.
Qed.  


Lemma sort_n_Sn : forall (n:nat) (l:list A),
  length l <= n -> sort_n n l = sort_n (S n) l.
Proof.
  (* induction on n *)
  intros n. elim n.
  (* n = 0 *)
  intros l H. cut (l = nil). intro H'. rewrite H'. simpl. reflexivity.
  apply length_zero_iff_nil. symmetry. apply le_n_0_eq. exact H.
  (* n -> n+1 *)(* induction on l *)
  clear n. intros n IH l. elim l.
  (* l = nil *)
  simpl. auto.
  (* l = (x::l') *)(* induction on l' *)
  clear l. intros x l' H. clear H. elim l'.
  (* l' = nil *)
  simpl. auto.
  (* l' = (a::l'') *)
  clear l'. intros a l'' H. clear H. intro H. pose (p:= S n). 
  change (sort_n (S n) (x :: a :: l'') = sort_n (S p) (x :: a :: l'')).
  unfold sort_n at 2. fold sort_n. unfold p. symmetry. 
  rewrite <- IH, <- IH. set (m:=sort_n n (a :: l'')). 
  symmetry. unfold sort_n at 1. fold sort_n. reflexivity.
  simpl. rewrite length_of_tl.  apply le_length_sort_n_n. 
  simpl in H. generalize H. case n. simpl. unfold not.
  intros H0 H1. clear H1. cut (0=S(length l'')). intro H1.
  discriminate H1. apply le_n_0_eq. apply le_S_n. exact H0.
  simpl.
  intros q. case l''. intros H1 H2. discriminate H2. 
  intros b m. case q. intro H0. simpl in H0. 
  cut (0 = S(length m)). intro H1. discriminate H1.
  apply le_n_0_eq. apply le_S_n. apply le_S_n. exact H0.
  intro r. intro H0. set (k := sort_n (S r) (b :: m)).
*)
