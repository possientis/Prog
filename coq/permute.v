Require Import List.
Require Import Relations.
Require Import list_lib.

(* inductive predicate expressing the fact that two lists are obtained from
each other, by the permutation of two consecutive elements  *)
Inductive Transpose {A:Type} : list A -> list A -> Prop :=
  | transp_refl :   forall (l: list A), Transpose l l
  | transp_pair :   forall(x y:A), Transpose (x::y::nil) (y::x::nil)
  | transp_gen  :   forall (l m l1 l2 : list A), 
    Transpose l m -> Transpose (l1++l++l2) (l1++m++l2).

(* one common issue with this sort of definition is that constructors of the
inductive predicates are akin to 'axioms', and it is very easy to define the
wrong thing, or things that are inconsistent, or incomplete etc *)

(* Here is another way to go about it *)
Definition Transpose' {A:Type} (l: list A) (m:list A) : Prop := 
  l = m \/ (exists (l1 l2:list A) (x y:A), 
  l = l1++(x::y::nil)++l2 /\ m = l1++(y::x::nil)++l2).

(* Transpose' is a reflexive relation on list A *)
Lemma Transpose_refl': forall (A:Type), reflexive (list A) Transpose'.
Proof.
  intros A. unfold reflexive. intros l. unfold Transpose'. left. reflexivity.
Qed. 

(* ideally, you want to check the equivalence between Transpose and Transpose' *)
Lemma Transpose_check: forall (A:Type), 
  same_relation (list A) Transpose Transpose'.
Proof.
  intros A. unfold same_relation. split. 
  unfold inclusion.
  intros l m. intro H. generalize H. elim H.
    clear H l m. intros l H. clear H. apply Transpose_refl'.
    clear H l m. intros x y H. clear H. unfold Transpose'. right.
      exists nil, nil, x, y. split; reflexivity.
    clear H l m. intros l m l1 l2 H0 H1 H2. clear H2.
      cut (Transpose' l m). clear H0 H1. intro H. 
      unfold Transpose' in H. elim H.
        clear H. intro H. rewrite H. apply Transpose_refl'.
        clear H. intro H. elim H. 
        clear H. intros l3 H. elim H.
        clear H. intros l4 H. elim H.
        clear H. intros x H. elim H.
        clear H. intros y H. unfold Transpose'. right.
          exists (l1++l3), (l4++l2), x, y. elim H.
            clear H. intros H0 H1. split.
            rewrite H0. set (k:= x::y::nil).
            rewrite <- app_assoc, <- app_assoc, <- app_assoc. reflexivity.
            rewrite H1. set (k:= y::x::nil). 
            rewrite <- app_assoc, <- app_assoc, <- app_assoc. reflexivity.
            apply H1. exact H0.
  unfold inclusion.
  intros l m H. unfold Transpose' in H. elim H. 
    clear H. intro H. rewrite H. apply transp_refl.
    clear H. intro H. elim H. 
      clear H. intros l1 H. elim H. 
      clear H. intros l2 H. elim H.
      clear H. intros x H. elim H.
      clear H. intros y H. elim H.
      clear H. intros Hl Hm. rewrite Hl, Hm.
      apply transp_gen. apply transp_pair.
Qed.

(* This version of the lemma can be handy for rewrites *)
Lemma Transpose_check': forall (A:Type) (l m: list A),
  Transpose l m <-> Transpose' l m.
Proof.
  intros A l m. split. 
    intro H. apply Transpose_check. exact H.
    intro H. apply Transpose_check. exact H.
Qed.

(* Transpose is a reflexive relation on list A *)
Lemma Transpose_refl: forall (A:Type), reflexive (list A) Transpose.
Proof.
   intros A. unfold reflexive. intros l. apply transp_refl.
Qed.

(* Transpose is a symmetric relation on list A *)
Lemma Transpose_sym: forall (A:Type), symmetric (list A) Transpose.
Proof.
  intros A. unfold symmetric. intros l m H. generalize H. elim H. 
    clear H l m. intros. apply transp_refl.
    clear H l m. intros. apply transp_pair.
    clear H l m. intros l m l1 l2 H0 H1 H2. clear H2. 
      apply transp_gen. apply H1. exact H0.
Qed.

(* Two lists which are transpositions of one another have same length *)
Lemma Transpose_imp_eq_length: forall (A:Type)(l m:list A),
  Transpose l m -> length l = length m.
Proof.
  intros A l m H. generalize H. elim H.
    clear H l m. intros. simpl. reflexivity. 
    clear H l m. intros. simpl. reflexivity.
    clear H l m. intros l m l1 l2 H0 H1 H2. clear H2.
  rewrite app_length, app_length, app_length, app_length.
  rewrite H1. reflexivity. exact H0.
Qed.

Lemma Transpose_l_nil: forall (A:Type)(l:list A),
  Transpose l nil -> l = nil.
Proof.
  intros A l H. apply length_zero_iff_nil. 
  apply Transpose_imp_eq_length with (m:=nil). exact H.
Qed.

Lemma Transpose_cons: forall (A:Type)(l m:list A)(a: A),
  Transpose l m -> Transpose (a::l) (a::m).
Proof.
 intros A l m a H. 
 cut (a::l = (a::nil) ++ l ++ nil).
 cut (a::m = (a::nil) ++ m ++ nil).
 intros Hm Hl. rewrite Hm, Hl. apply transp_gen. exact H.
 rewrite <- app_comm_cons. rewrite app_nil_l. rewrite app_nil_r. reflexivity.
 rewrite <- app_comm_cons. rewrite app_nil_l. rewrite app_nil_r. reflexivity.
Qed.

Lemma Transpose_cons_reverse: forall (A:Type)(l m:list A)(a:A),
  Transpose (a::l) (a::m) -> Transpose l m.
Proof.
  intros A l m a.
  cut (forall (l' m':list A), 
    l' = a::l -> m' = a::m -> Transpose l' m' -> Transpose l m). eauto.
  intros l' m' Hl Hm H. generalize H Hl Hm. 
  clear Hl Hm. generalize l m a. clear l m a. elim H. 
    clear H l' m'. intros k l m a H0 H1 H2. clear H0. 
      rewrite H1 in H2. clear H1. injection H2. intros H0.
      rewrite H0. apply Transpose_refl.
    clear H l' m'. intros x y l m a H0 H1 H2. clear H0.
      injection H1. clear H1. injection H2. clear H2.
      intros H0 H1 H2 H3. 
      rewrite H3 in H0. clear H3. rewrite H1 in H2. clear H1.
      rewrite H2 in H0. clear H2. rewrite H0. apply Transpose_refl.
    clear H l' m'. intros l m l1 l2 H0 H1 l' m' a H2 H3 H4.
      generalize (destruct_list l1). intro H5. elim H5.
        clear H5. intro H5. elim H5. clear H5. intros x H5. elim H5.
          clear H5. intros k1 H5. rewrite H5 in H3. rewrite H5 in H4.
          rewrite <- app_comm_cons in H3. rewrite <- app_comm_cons in H4.
          injection H3. injection H4. clear H3 H4 H5. intros H3 H4. clear H4.
          intros H4 H5. clear H5. rewrite <- H3, <- H4. clear H3 H4.
          apply transp_gen. exact H0.
        clear H5. intro H5. rewrite H5 in H3. rewrite H5 in H4.
          rewrite app_nil_l in H3. rewrite app_nil_l in H4. clear H2 H5.
          generalize (destruct_list l). generalize (destruct_list m).
          intros H5 H6. elim H5.
            clear H5. intro H5. elim H5. clear H5. intros b H5. elim H5.
              clear H5. clear l1. intros l1 H5. rewrite H5 in H4.
              rewrite <- app_comm_cons in H4. injection H4. clear H4.
              intro H4. intro H7. rewrite H7 in H5. clear H7 b. elim H6.
                clear H6. intro H6. elim H6. clear H6. intros b H6. elim H6.
                  clear H6. intros k1 H6. rewrite H6 in H3.
                  rewrite <- app_comm_cons in H3. injection H3. clear H3.
                  intro H3. intro H7. rewrite H7 in H6. clear H7 b. 
                  rewrite <- app_nil_l with (l:=k1++l2) in H3. rewrite <- H3. 
                  rewrite <- app_nil_l with (l:=l1++l2) in H4. rewrite <- H4.
                  apply transp_gen. apply H1 with (a:=a). exact H0. 
                  exact H6. exact H5.
                clear H6. intro H6. rewrite H6 in H0. apply Transpose_sym in H0.
                  apply Transpose_l_nil in H0. rewrite H0 in H5. discriminate H5.
            clear H5. intro H5. rewrite H5 in H0. apply Transpose_l_nil in H0.
              rewrite H0 in H3. rewrite app_nil_l in H3.
              rewrite H5 in H4. rewrite app_nil_l in H4. rewrite H3 in H4. 
              injection H4. clear H4. intro H4. rewrite H4. apply Transpose_refl.
Qed.


(* This inductive predicate expresses the fact that two 
lists are permutation of one another *)
Inductive Permute {A:Type} : list A -> list A -> Prop :=
  | perm_refl : forall l:list A, Permute l l
  | perm_next : forall l l' m: list A, 
    Permute l l' -> Transpose l' m -> Permute l m. 


(* Permute is a reflexive relation on list A *)
Lemma Permute_refl : forall (A:Type), reflexive (list A) Permute.
Proof.
  intros A. unfold reflexive. intros l. apply perm_refl.
Qed.

(* As defined, the Permute relation is such that if l1 is
  a permutation of l2 and l2 is a transposition of l3, then
  l1 is deemed a permutation of l3. In order to prove that 
  the Permute relation is symmetric, we need to be able to 
  argue the other way around, namely that if l1 is a 
  transposition of l2 and l2 is a permutation of l3, then
  l1 is also a permutation of l3. This result is obvious 
  once we have established the symmetry of both Transpose
  and Permute, but we are not there yet. *)
Lemma Transpose_first: forall (A:Type) (l l' m:list A),
  Transpose l l' -> Permute l' m -> Permute l m.
Proof.
  intros A l l' m H0 H1. generalize H0. clear H0. generalize H1 l. 
  elim H1. clear H1 l l' m. intros m. intro H. clear H. intro l.
  intro H. apply perm_next with (l':=l). apply perm_refl. exact H.
  clear H1 l l' m. intros l l' m H0 H1 H3 H4 k H5.
  eapply perm_next. apply H1. exact H0. exact H5. exact H3.
  (* dont understand why normal 'apply ... with' was failing *)
Qed.

(* We are now in a position to prove the symmetry of Permute *)
Lemma Permute_sym: forall (A:Type), symmetric (list A) Permute.
Proof.
  intro A. unfold symmetric.
  intros l m H. generalize H. elim H. auto. clear H m l.
  intros l l' m H0 H1 H2 H3. apply Transpose_first with (l':=l').
  apply Transpose_sym. exact H2. apply H1. exact H0.
Qed.

(* Permute is also a transitive relation on list A *)
Lemma Permute_trans: forall (A:Type), transitive (list A) Permute.
Proof.
  intros A. unfold transitive.
  intros l m k H. generalize H k. clear k. elim H. auto.
  clear H l m. intros l l' m H0 H1 H2 H3 k H4.
  apply H1. exact H0. apply Transpose_first with (l':=m).
  exact H2. exact H4.
Qed.


(* Two lists which are permutation of one another have same length *)
Lemma Permute_imp_eq_length: forall (A:Type)(l m:list A),
  Permute l m -> length l = length m.
Proof.
  intros A l m H. generalize H. elim H.
  clear H l m. intros. reflexivity.  
  clear H l m. intros l l' m H0 H1 H2 H3. clear H3.  
  apply eq_trans with (y:=length l').
  apply H1. exact H0. apply Transpose_imp_eq_length. exact H2.
Qed.

Lemma Permute_cons: forall (A:Type)(l m: list A)(a: A),
  Permute l m -> Permute (a::l) (a::m).
Proof.
  intros A l m a H. generalize H. generalize a. clear a. elim H.
    clear H l m. intros. apply perm_refl.
    clear H l m. intros l l' m H0 H1 H2 a H3.
  apply (Permute_trans A (a::l) (a::l') (a::m)). apply H1. exact H0.
  apply (perm_next (a::l') (a::l') (a::m)). apply perm_refl.
  apply Transpose_cons. exact H2.
Qed.


Definition SubSet {A:Type}(l m:list A) : Prop :=
  forall (x:A), In x l -> In x m.

Definition EqSet {A:Type}(l m: list A) : Prop :=
  SubSet l m /\ SubSet m l.

Lemma SubSet_refl: forall (A:Type), reflexive (list A) SubSet.
Proof.
  intros A. unfold reflexive. intro l. unfold SubSet. auto.
Qed.

Lemma SubSet_trans: forall (A: Type), transitive (list A) SubSet.
Proof.
  intros A. unfold transitive.
  intros l m k H0 H1. unfold SubSet. intros x H2.
  apply H1. apply H0. exact H2.
Qed.


Lemma Transpose_imp_SubSet: forall (A:Type), 
  inclusion (list A) Transpose SubSet.
Proof.
  intros A. unfold inclusion.
  intros l m H. generalize H. elim H.
    clear H l m. intros. apply SubSet_refl.
    clear H l m. intros x y H0. clear H0. unfold SubSet.
      intros z H0. simpl. simpl in H0. elim H0.
        clear H0. intro H0. right. left. exact H0.
        clear H0. intro H0. elim H0. clear H0. intro H0. left. exact H0.
          apply False_ind.
    clear H l m. intros l m l1 l2 H0 H1 H2. clear H2. unfold SubSet.
      intros x H2. simpl. rewrite in_app_iff, in_app_iff.
      rewrite in_app_iff, in_app_iff in H2. elim H2.
        clear H2. intro H2. left. exact H2.
        clear H2. intro H2. elim H2. clear H2. intro H2. right. left.
          apply H1. exact H0. exact H2.
        clear H2. intro H2. right. right. exact H2.
Qed.

Lemma Transpose_imp_EqSet: forall (A:Type),
  inclusion (list A) Transpose EqSet.
Proof.
  intros A. unfold inclusion.
  intros l m H. unfold EqSet. split. 
  apply Transpose_imp_SubSet. exact H.
  apply Transpose_imp_SubSet. apply Transpose_sym. exact H.
Qed.

Lemma Permute_imp_SubSet: forall (A:Type), 
  inclusion (list A) Permute SubSet.
Proof.
  intros A. unfold inclusion.
  intros l m H. generalize H. elim H.
    clear H l m. intros. apply SubSet_refl.
    clear H l m. intros l l' m H0 H1 H2 H3. clear H3.
      apply (SubSet_trans A l l' m). apply H1. exact H0.
      apply Transpose_imp_SubSet. exact H2.
Qed.

Lemma Permute_imp_EqSet: forall (A:Type),
  inclusion (list A) Permute EqSet.
Proof.
  intros A. unfold inclusion.
  intros l m H. unfold EqSet. split.
  apply Permute_imp_SubSet. exact H.
  apply Permute_imp_SubSet. apply Permute_sym. exact H.
Qed.


Lemma Permute_cons_reverse: forall (A:Type)(l m:list A)(a:A),
  Permute (a::l) (a::m) -> Permute l m.
Proof.
  intros A l m a.
  cut (forall (l' m':list A), 
    l' = a::l -> m' = a::m -> Permute l' m' -> Permute l m). eauto.
  intros l' m' Hl Hm H. generalize H Hl Hm.
  clear Hl Hm. generalize l m a. clear l m a. elim H.
    clear H l' m'. intros l m' m a H0 H1 H2. clear H0. 
      rewrite H2 in H1. clear H2. injection H1. clear H1. 
      intro H0. rewrite H0. apply perm_refl.
    clear H l' m'. intros l' k' m' H0 H1 H3 l m a H4 H5 H6.



