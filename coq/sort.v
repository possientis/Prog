Require Import List.
Require Import Arith.
Require Import Bool.

Parameter A:Type.
Parameter R: A -> A -> Prop.
Parameter R_bool: A -> A -> bool.
Axiom R_refl:   forall x:A, R x x.
Axiom R_anti:   forall x y:A, R x y -> R y x -> x = y.
Axiom R_trans:  forall x y z:A, R x y -> R y z -> R x z.
Axiom R_total:  forall x y:A, R x y \/ R y x.
Axiom R_lem:    forall x y:A, R x y <-> R_bool x y = true.

Lemma not_none_is_some : forall (A:Type) (o: option A),
  o <> None -> exists x:A, o = Some x.
Proof.
  intros A o. elim o. intros a H. exists a. reflexivity.
  intro H. apply False_ind. apply H. reflexivity.
Qed.

Lemma none_or_not_none : forall (A:Type) (o:option A),
  o = None \/ o <> None.
Proof.
  intros A o. elim o. intro a. right. intro H. discriminate.
  left. reflexivity.
Qed.

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

(* defining inductive predicate: Least a l <-> Some a = least l *)
Inductive  Least : A -> list A -> Prop :=
  | Least_single : forall a:A, Least a (a::nil)
  | Least_cons1  : forall (a b:A)(l:list A),
      Least a l -> R a b -> Least a (b::l)
  | Least_cons2  : forall (a b:A)(l:list A),
      Least a l -> R b a -> Least b (b::l). 



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

Lemma least_imp_Least: forall (a:A)(l:list A),
  least l = Some a -> Least a l.
Proof. 
  (*induction on l *)
  intros a l. generalize a. clear a. elim l.
  (* l = nil *)
  simpl. intros a H. discriminate H.
  (* l = (a::l') *)
  clear l. intros a l IH b H. simpl in H.
  generalize H IH. set (ll := least l).
  elim ll. intros c H0 H1. elim (R_total a c).
  intro Rac. rewrite R_lem in Rac.
  rewrite Rac in H0. 
  pose (g:= (fun o => match o with | None => a | Some x => x end)).
  fold (g (Some b)). rewrite <- H0. unfold g.
  apply Least_cons2 with (a:=c). apply H1. reflexivity.
  apply R_lem. exact Rac.
  intro Rca. apply Least_cons1. apply H1.
  cut ({R_bool a c = true} + { R_bool a c <> true}).
  intros Lac. elim Lac. intro Rac. rewrite Rac in H0.
  rewrite <- R_lem in Rac. cut (a = c). intro Eac.
  rewrite <- Eac. exact H0. apply R_anti. exact Rac. exact Rca.
  intro Rac. cut (R_bool a c = false). intro Rac'.
  rewrite Rac' in H0. exact H0. apply not_true_is_false.
  exact Rac. apply bool_dec.
  cut ({R_bool a c = true} + { R_bool a c <> true}).
  intros Lac. elim Lac. intro Rac. rewrite Rac in H0.
  injection H0. intro Eab. rewrite Eab. apply R_refl.
  intro Rac. cut (R_bool a c = false). intro Rac'.
  rewrite Rac' in H0. injection H0. intro Ecb.
  rewrite <- Ecb. exact Rca. apply not_true_is_false.
  exact Rac. apply bool_dec. intro Eab. intro H'. clear H'.
  injection Eab. clear Eab. intro Eab. rewrite <- Eab.
  rewrite <- Eab in H. clear Eab b. fold ll in H.
  fold ll in IH. cut (ll = None \/ ll <> None).
  intro Hll. elim Hll. intro Nonell. cut (l=nil).
  intro lnil. rewrite lnil. apply Least_single.
  apply least_none. exact Nonell. intro H'.
  cut (exists c:A, ll = Some c). intro H0.
  elim H0. intro c. intro Hc. rewrite Hc in H.
  cut (R a c \/ R c a). intro H1. elim H1.
  intro Rac. apply Least_cons2 with (a:=c).
  apply IH. exact Hc. exact Rac. intro Rca.
  cut ({R_bool a c = true} + {R_bool a c <> true}).
  intro H2. elim H2. intro Rac. cut (a = c).
  intro Eac. apply Least_cons1. rewrite Eac.
  apply IH. exact Hc. apply R_refl. apply R_anti.
  apply R_lem. exact Rac. exact Rca. intro Rac.
  cut (R_bool a c = false). intro Rac'.
  rewrite Rac' in H. injection H. intro Eca.
  apply Least_cons1. rewrite <- Eca. apply IH.
  exact Hc. apply R_refl. apply not_true_is_false.
  exact Rac. apply bool_dec. apply R_total.
  apply not_none_is_some. exact H'.
  apply none_or_not_none.
Qed.

Lemma Least_imp_least: forall (a:A)(l:list A),
  Least a l -> least l = Some a.
Proof. 
  intros a l HL. generalize HL. elim HL. 
  simpl. auto. clear a l HL. intros a b l H0 H1 H2 H3.
  simpl. rewrite H1. cut ({R_bool b a = true} + {R_bool b a <> true}). 
  intro H4. elim H4. intro H5. rewrite H5. cut (a = b). intro Eab.
  rewrite <- Eab. reflexivity. apply R_anti. exact H2. apply R_lem.
  exact H5. intro H5. cut(R_bool b a = false). intro H6. rewrite H6.
  reflexivity. apply not_true_is_false. exact H5. apply bool_dec.
  exact H0. clear a l HL. intros a b l H0 H1 H2 H3. simpl.
  rewrite H1. rewrite R_lem in H2. rewrite H2. reflexivity. exact H0.
Qed.




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
