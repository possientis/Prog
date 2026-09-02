(* coqtop -lv filename -I LibDirectory *)

Require Import option.      (* personal *)
Require Import list.        (* personal *)
Require Import permute.     (* personal *)

Require Import List.
Require Import Arith.
Require Import Bool.

(******************************************************************************)
(*                               Assumptions                                  *)
(******************************************************************************)

Parameter A:Type.
Parameter R: A -> A -> Prop.
Parameter R_bool: A -> A -> bool.
Axiom R_refl:   forall x:A, R x x.
Axiom R_anti:   forall x y:A, R x y -> R y x -> x = y.
Axiom R_trans:  forall x y z:A, R x y -> R y z -> R x z.
Axiom R_total:  forall x y:A, R x y \/ R y x.
Axiom R_lem:    forall x y:A, R x y <-> R_bool x y = true.

Lemma R_or_not_R: forall x y:A, R x y \/ ~R x y.
Proof.
  intros x y.
  generalize (bool_dec (R_bool x y) true). intro H. elim H.
  clear H. intro H. left. rewrite R_lem. exact H.
  clear H. intro H. right. rewrite R_lem. exact H.
Qed.

Lemma A_dec: forall x y: A, x = y \/ x <> y.
Proof.
  intros x y. generalize (R_total x y). intro H. elim H.
  clear H. intro H. generalize (R_or_not_R y x). intro H'. elim H'.
  clear H'. intro H'. left. apply R_anti. exact H. exact H'.
  clear H'. intro H'. right. intro Eq. apply H'.
  rewrite Eq. rewrite Eq in H. exact H.
  clear H. intro H. generalize (R_or_not_R x y). intro H'. elim H'.
  clear H'. intro H'. left. apply R_anti. exact H'. exact H.
  clear H'. intro H'. right. intro Eq. apply H'.
  rewrite Eq. rewrite Eq in H. exact H.
Qed.


(******************************************************************************)
(*                                 Least                                      *)
(******************************************************************************)

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
  least l = Some a -> Least a l.  Proof. 
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


Theorem Least_is_least: forall (a:A)(l:list A),
  Least a l <-> least l = Some a.
Proof.
  intros a l. split. apply Least_imp_least. apply least_imp_Least. 
Qed.


(* We spent a fair amount of effort defining an inductive predicate Least
and proving the equivalence Least a l <-> least l= Some a. This effort is
now paying off, as proving properties of 'Least' is a lot easier than 
dealing with 'least'. Try proving the following lemma in terms of 'least'
directly, and this will be plainly obvious *)

Lemma Least_imp_In: forall (a:A)(l:list A),
  Least a l -> In a l.
Proof.
  intros a l H. generalize H. elim H.
  simpl. auto. 
  clear H a l. intros a b l H0 H1 H2 H3. simpl. right. apply H1. exact H0.
  clear H a l. intros a b l H0 H1 H2 H3. simpl. auto.
Qed.

Lemma Least_imp_smaller: forall (a b:A)(l: list A),
  Least a l -> In b l -> R a b.
Proof.
  intros a b l H. generalize H b. clear b. elim H.
  clear H a l. intros a H0 b H1. 
  simpl in H1. elim H1. intro Eab. rewrite Eab. apply R_refl. apply False_ind.
  clear H a l. intros a b l H0 H1 H2 H3 c H4. simpl in H4. elim H4.
  intro Ebc. rewrite <- Ebc. exact H2. apply H1. exact H0.
  clear H a l. intros a b l H0 H1 H2 H3 c H4. simpl in H4. elim H4.
  intro Ebc. rewrite Ebc. apply R_refl. intro H5. apply R_trans with (y:= a). 
  exact H2. apply H1. exact H0. exact H5.
Qed.

Lemma not_nil_exists_Least: forall (l:list A),
  l <> nil <-> exists a:A, Least a l.
Proof.
  intro l. split. intro H. cut (least l = None \/ least l <> None).
  intro H0. elim H0. intro H1. rewrite least_none in H1.
  apply False_ind. apply H. exact H1. intro H1.
  rewrite not_none_is_some in H1. elim H1.
  intros x Hx. exists x. rewrite Least_is_least. exact Hx.
  apply none_or_not_none. intro H. elim H. intros x Hx.
  rewrite Least_is_least in Hx. intro H0. rewrite <- least_none in H0. 
  rewrite H0 in Hx. discriminate.
Qed.

Lemma smallest_imp_Least: forall (a:A)(l:list A),
  In a l -> (forall b:A, In b l -> R a b) -> Least a l. 
Proof.
  intros a l. generalize a. clear a. elim l. 
  simpl. intros a F. apply False_ind. exact F.
  clear l. intros b l IH a H0 H1. simpl.
  cut (l = nil \/ l <> nil). intro H2. elim H2. clear H2. intro H2.
  rewrite H2. simpl in H0. elim H0. intros Eba. rewrite Eba.
  apply Least_single. rewrite H2. clear H2. intro H2. simpl in H2.
  apply False_ind. exact H2. clear H2. intro H2.
  rewrite not_nil_exists_Least in H2. elim H2. intros a' Ha'.
  simpl in H0. elim H0. intro Eba. rewrite <- Eba.
  apply Least_cons2 with (a:=a'). exact Ha'. rewrite Eba.
  apply H1. simpl. right. apply Least_imp_In. exact Ha'.
  intro Ha. cut (a = a'). intro Ea. rewrite Ea. apply Least_cons1.
  exact Ha'. rewrite <- Ea. apply H1. simpl. left. reflexivity.
  apply R_anti. apply H1. simpl. right. apply Least_imp_In.
  exact Ha'. apply Least_imp_smaller with (l:=l). exact Ha'. exact Ha.
  apply nil_or_not_nil.
Qed.

(******************************************************************************)
(*                           Sorted list                                      *)
(******************************************************************************)

(* a possible definition as an inductive predicate *)
Inductive Sorted : list A -> Prop :=
  | SortedNil : Sorted nil
  | SortedCons: forall (a :A) (l:list A), 
      Least a (a::l) -> Sorted l -> Sorted (a::l).

(* a possible definition as a boolean function *)
Fixpoint isSorted (l:list A) : bool :=
  match l with
    | nil     => true
    | (a::l') => match least l' with
                  | None    =>  true
                  | Some b  =>  match R_bool a b with
                                  | true   => isSorted l'
                                  | false  => false
                                end 
                 end
  end. 


(* before proceeding, we need to make sure the two notions are equivalent *)
Lemma Sorted_imp_isSorted: forall (l:list A), 
  Sorted l -> isSorted l = true.
Proof.
  intros l H. generalize H. elim H.
  clear H l. simpl. auto.
  clear H l. intros a l H0 H1 H2 H3. simpl.
  set (L := least l). cut (L = least l -> 
    match L with | Some b => if R_bool a b then isSorted l else false
                 | None => true
    end = true). eauto. generalize H0 H1 H2 H3. clear H0 H1 H2 H3.
  generalize a. clear a. elim L; auto. intros b a H0 H1 H2 H3 H4.
  cut (R_bool a b = true). intro H5. rewrite H5. apply H2. exact H1.
  rewrite <- R_lem. apply Least_imp_smaller with (l:= a::l). exact H0.
  simpl. right. apply Least_imp_In. apply Least_is_least. symmetry. exact H4.
Qed.

Lemma isSorted_a_b_Rab: forall (a b:A)(l:list A),
  isSorted (a::b::l) = true -> R a b.
Proof.
  intros a b l H. unfold isSorted in H. fold isSorted in H.
  set (L:= least (b::l)). cut (L = least (b::l) -> R a b). eauto.
  fold L in H. generalize H. clear H. generalize a. clear a. elim L.
  clear L. intros L a H0 H1. set (b1 := R_bool a L). fold b1 in H0.
  cut (b1 = R_bool a L -> R a b). eauto. generalize H0. clear H0.
  case b1. intros H0 H2. clear H0. apply R_trans with (y:= L).
  rewrite R_lem. symmetry. exact H2. apply Least_imp_smaller with (l:=b::l).
  rewrite Least_is_least. symmetry. exact H1. simpl. left. reflexivity.
  intros. discriminate.
  intros a H0 H1. symmetry in H1. rewrite least_none in H1. discriminate.
Qed.

Lemma isSorted_a_b_isSorted_a: forall (a b:A)(l: list A),
  isSorted(a::b::l) = true -> isSorted(a::l) = true.
Proof.
  intros a b l H. unfold isSorted in H. fold isSorted in H.
  set (L:= least (b::l)). cut (L = least (b::l) -> isSorted (a::l) = true). eauto.
  fold L in H. generalize H. clear H. generalize a. clear a. elim L.
  clear L. intros L a H0 H1. set (b1 := R_bool a L). fold b1 in H0.
  cut (b1 = R_bool a L -> isSorted (a :: l) = true). eauto. generalize H0. clear H0.
  case b1. intros H0 H2. unfold isSorted. fold isSorted. 
  set (L':= least l). cut (L' = least l ->  match L' with 
    | Some b0 => if R_bool a b0 then isSorted l else false
    | None => true
  end = true). eauto. fold L' in H0. generalize H0. clear H0. elim L'.
  clear L'. intros L' H0 H3.
  set (b2 := R_bool b L'). fold b2 in H0. generalize H0. clear H0. elim b2.
  intros H0. cut (R_bool a L' = true). intro H4. rewrite H4. exact H0.
  rewrite <- R_lem. apply R_trans with (y:=L). 
  rewrite R_lem. symmetry. exact H2. apply Least_imp_smaller with (l:= b::l).
  apply Least_is_least. symmetry. exact H1. simpl. right. apply Least_imp_In.
  apply Least_is_least. symmetry. exact H3.
  intros. discriminate. 
  intros. auto.
  intros. discriminate.
  intros a H0 H1. clear H0. 
  symmetry in H1. rewrite least_none in H1. discriminate.
Qed.
  
Lemma isSorted_head_smallest: forall (a:A)(l:list A),
  isSorted (a::l) = true -> (forall b:A, In b l -> R a b).
Proof.
  intros a l. generalize a. clear a. elim l.
  clear l. intros a H0 b H1. simpl in H1. apply False_ind. exact H1.
  clear l. intros b l IH a H0 c H1. 
  simpl in H1. elim H1. 
  clear H1. intro H1. rewrite <- H1. 
  apply isSorted_a_b_Rab with (l:=l). exact H0.
  clear H1. intro H1. apply IH.
  apply isSorted_a_b_isSorted_a with (b:=b). exact H0. exact H1.
Qed.


Lemma isSorted_tail: forall (a:A)(l:list A),
  isSorted (a::l) = true -> isSorted l = true.
Proof.
  intros a l H. simpl in H. set (L := least l). fold L in H. 
  cut (L = least l -> isSorted l = true). eauto. 
  generalize H. clear H. elim L.
  clear L. intros L H0 H1. set (b1 := R_bool a L). fold b1 in H0.
  generalize H0. clear H0. elim b1. auto. intros. discriminate.
  intros H0 H1. symmetry in H1. rewrite least_none in H1. rewrite H1.
  simpl. reflexivity.
Qed.

Lemma isSorted_imp_Sorted: forall (l:list A),
  isSorted l = true -> Sorted l.
Proof.
  intros l. elim l.
  clear l. intros. apply SortedNil.
  clear l. intros a l IH H. apply SortedCons.
  generalize H IH. clear H IH. generalize a. clear a. elim l.
  clear l. intros. apply Least_single.
  clear l. intros b l H0 a H1 H2. apply smallest_imp_Least.
  simpl. left. reflexivity.
  intros c Hc. simpl in Hc. elim Hc. 
  clear Hc. intros Hc. rewrite Hc. apply R_refl.
  clear Hc. intro Hc. elim Hc.
  clear Hc. intro Hc. rewrite <- Hc.
  apply isSorted_head_smallest with (l:= b::l). exact H1.
  simpl. left. reflexivity.
  clear Hc. intro Hc. apply isSorted_head_smallest with (l:= b::l).
  exact H1. simpl. right. exact Hc.
  apply IH. apply isSorted_tail with (a:=a). exact H.
Qed.

Theorem  Sorted_is_isSorted: forall (l:list A),
  Sorted l <-> isSorted l = true.
Proof.
  intro l. split. apply Sorted_imp_isSorted. apply isSorted_imp_Sorted.
Qed.


(******************************************************************************)
(*                           The sort function                                *)
(******************************************************************************)

(* our definition of sort is based on insert *)
Fixpoint insert (a:A)(l:list A) : list A :=
  match l with
    | nil       => (a::nil)
    | (b::l')   => match R_bool a b with
                    | true      => (a::l)
                    | false     => (b::insert a l')
                  end
  end.

Fixpoint sort (l:list A) : list A :=
  match l with
    | nil       => nil
    | (a::l')   => insert a (sort l')
  end.

(******************************************************************************)
Fixpoint qsort (l:list A) : list A :=
  match l with
    | nil       => nil
    | (x::l')   => let lhs := l' in (* TODO *)
                   let rhs := l' in (* TODO *)
                      qsort lhs ++ (x::nil) ++ qsort rhs
  end.

(* is sort = qsort TODO *)
(* is sort idempotent TODO *)
(******************************************************************************)

Lemma In_insert_In: forall (l:list A)(a x:A),
  In x (insert a l) -> x = a \/ In x l.
Proof.
  intros l. elim l.
  clear l. simpl. intros a x H. elim H. 
  clear H. intro H. left. symmetry. exact H.
  clear H. apply False_ind.
  clear l. intros b l IH a x H. set (b1:= R_bool a b). 
  cut (b1 = R_bool a b ->  x = a \/ In x (b :: l)). eauto. elim b1.
  clear b1. intro H0. simpl in H. rewrite <- H0 in H. simpl in H. elim H.
  clear H. intro H. left. symmetry. exact H.
  clear H. intro H. elim H.
  clear H. intro H. right. simpl. left. exact H.
  clear H. intro H. right. simpl. right. exact H.
  clear b1. intro H0. simpl in H. rewrite <- H0 in H. simpl in H. elim H.
  clear H. intro H. right. simpl. left. exact H.
  clear H. intro H. apply IH in H. elim H.
  clear H. intro H. left. exact H.
  clear H. intro H. right. simpl. right. exact H.
Qed.

Lemma Sorted_insert: forall (l:list A)(a:A),
  Sorted l -> Sorted (insert a l).
Proof.
  intros l. elim l.
  clear l. simpl. intros. apply SortedCons. apply Least_single. apply SortedNil. 
  clear l. intros a l IH b H0. set (b1:= R_bool b a). 
  cut (b1 = R_bool b a -> Sorted (insert b (a :: l))). eauto. elim b1.
  clear b1. intro H1. simpl. rewrite <- H1. apply SortedCons.
  apply smallest_imp_Least. simpl. left. reflexivity. intros c Hc.
  simpl in Hc. elim Hc.
  clear Hc. intro Hc. rewrite Hc. apply R_refl.
  clear Hc. intro Hc. elim Hc. clear Hc. intro Hc. rewrite <- Hc.
  rewrite R_lem. symmetry. exact H1.
  clear Hc. intro Hc. apply R_trans with (y:=a). rewrite R_lem.
  symmetry. exact H1. apply isSorted_head_smallest with (l:=l).
  rewrite <- Sorted_is_isSorted. exact H0. exact Hc. exact H0.
  clear b1. intro H1. simpl. rewrite <- H1. apply SortedCons.
  apply smallest_imp_Least. simpl. left. reflexivity.
  intros c Hc. simpl in Hc. elim Hc.
  clear Hc. intro Hc. rewrite Hc. apply R_refl.
  clear Hc. intro Hc. apply In_insert_In in Hc. elim Hc. 
  clear Hc. intro Hc. rewrite Hc. clear Hc. generalize (R_total a b).
  intro H2. elim H2. auto. clear H2. intro H2. rewrite R_lem in H2.
  rewrite H2 in H1. discriminate.
  clear Hc. intro Hc. apply isSorted_head_smallest with (l:=l).
  rewrite <- Sorted_is_isSorted. exact H0. exact Hc.
  apply IH. rewrite Sorted_is_isSorted. apply isSorted_tail with (a:=a).
  rewrite <- Sorted_is_isSorted. exact H0.
Qed.

(* This partially justifies our definition of sort *)
Theorem Sorted_sort: forall (l:list A), Sorted (sort l).
Proof.
  intro l. elim l.
  clear l. simpl. apply SortedNil.
  clear l. intros a l IH. simpl. apply Sorted_insert. exact IH.
Qed.


(* the lists (insert a l) and (a::l) are permutation of one another *)
Lemma Permute_insert: forall (l:list A)(a:A),
  Permute (insert a l) (a::l).
Proof.
  intros l. elim l.  
  clear l. intros a. simpl. apply perm_self.
  clear l. intros b l IH a. set (b1:=R_bool a b).
  cut (b1 = R_bool a b ->  Permute (insert a (b :: l)) (a :: b :: l)). 
  eauto. elim b1.
  clear b1. intro H. simpl. rewrite <- H. apply perm_self.
  clear b1. intro H. simpl. rewrite <- H.
  apply Permute_trans with (m:= (b::a::l)). apply Permute_cons. apply IH. 
  apply (perm_next (b::a::l) (b::a::l) (a::b::l)). apply perm_self.
  cut (b::a::l = nil++(b::a::nil)++l).
  cut (a::b::l = nil++(a::b::nil)++l).
  intros H0 H1. rewrite H0, H1. apply transp_gen. apply transp_pair.
  rewrite app_nil_l, <- app_comm_cons, <- app_comm_cons, app_nil_l. reflexivity.
  rewrite app_nil_l, <- app_comm_cons, <- app_comm_cons, app_nil_l. reflexivity.
Qed.
  
(* This also partially justifies our definition of sort *)
Theorem Permute_sort: forall (l:list A), Permute (sort l) l.
Proof.
  intros l. elim l.
  clear l. simpl. apply perm_self. 
  clear l. intros a l IH. simpl. apply Permute_trans with (m:=(a::(sort l))).
  apply Permute_insert. apply Permute_cons. exact IH.
Qed.


(* Permute l l' -> Sorted l -> Sorted l' -> l = l' ?? *)





