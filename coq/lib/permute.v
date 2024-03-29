Require Import List.

(* inductive predicate expressing the fact that two lists are obtained from
each other, by the Permute of two consecutive elements  *)
Inductive Transpose {A:Type} : list A -> list A -> Prop :=
  | transp_pair : forall(x y:A), Transpose (x::y::nil) (y::x::nil)
  | transp_gen  : forall (l m l1 l2 : list A), 
    Transpose l m -> Transpose (l1++l++l2) (l1++m++l2).

(* one common issue with this sort of definition is that constructors of the
inductive predicates are akin to 'axioms', and it is very easy to define the
wrong thing, or things that are inconsistent, or incomplete etc *)

(* Here is another way to go about it *)
Definition Transpose' {A:Type} (l: list A) (m:list A) : Prop := 
  exists (l1 l2:list A) (x y:A), 
  l = l1++(x::y::nil)++l2 /\ m = l1++(y::x::nil)++l2.

(* ideally, you want to check the equivalence between the two notions *)
Lemma Transpose_check: forall (A:Type)(l m:list A),
  Transpose l m <-> Transpose' l m.
Proof.
  intros A l m. split. intro H. generalize H. elim H. intros. 
  unfold Transpose'. exists nil, nil, x, y. auto.
  clear H l m. intros l m l1 l2 H0 H1 H2. clear H2.
  cut (Transpose' l m). clear H0 H1. intro H.
  unfold Transpose' in H. elim H. intro l3. clear H. intro H.
  elim H. intro l4. clear H. intro H. 
  elim H. intro x. clear H. intro H.
  elim H. intro y. clear H. intro H.
  elim H. clear H. intros H0 H1.
  unfold Transpose'.
  exists (l1++l3), (l4++l2), x, y. rewrite H0, H1. clear H0 H1.
  split. rewrite <- app_assoc with (l:=l1). rewrite <- app_assoc with (l:=l3).
  rewrite <- app_assoc with (n:=l2). reflexivity. 
  rewrite <- app_assoc with (l:=l1). rewrite <- app_assoc with (l:=l3).
  rewrite <- app_assoc with (n:=l2). reflexivity.
  apply H1. exact H0.
  intro H. unfold Transpose' in H. elim H. clear H. intros l1 H.
  elim H. clear H. intros l2 H. elim H. clear H. intros x H.
  elim H. clear H. intros y H. elim H. clear H. intros Hl Hm.
  rewrite Hl, Hm. apply transp_gen. apply transp_pair.
Qed.

(* This inductive predicate expresses the fact that two 
lists are Permutes of one another *)
Inductive Permute {A:Type} : list A -> list A -> Prop :=
  | perm_self : forall l:list A, Permute l l
  | perm_next : forall l l' m: list A, 
    Permute l l' -> Transpose l' m -> Permute l m. 


Lemma Permute_refl : forall (A:Type) (l:list A), Permute l l.
Proof.
  intros A l. apply perm_self.
Qed.

 
Lemma Transpose_sym: forall (A:Type) (l m: list A),
  Transpose l m -> Transpose m l.
Proof.
  intros A l m H. generalize H. elim H. clear l m H.
  intros x y H. clear H. apply transp_pair. clear l m H.
  intros l m l1 l2 H H' H0. clear H0. apply transp_gen.
  apply H'. exact H.
Qed.

Lemma Transpose_first: forall (A:Type) (l l' m:list A),
  Transpose l l' -> Permute l' m -> Permute l m.
Proof.
  intros A l l' m H0 H1. generalize H0. clear H0. generalize H1 l. 
  elim H1. clear H1 l l' m. intros m. intro H. clear H. intro l.
  intro H. apply perm_next with (l':=l). apply perm_self. exact H.
  clear H1 l l' m. intros l l' m H0 H1 H3 H4 k H5.
  eapply perm_next. apply H1. exact H0. exact H5. exact H3.
  (* dont understand why normal 'apply ... with' was failing *)
Qed.

Lemma Permute_sym: forall (A:Type) (l m: list A),
  Permute l m -> Permute m l.
Proof.
  intros A l m H. generalize H. elim H. auto. clear H m l.  
  intros l l' m H0 H1 H2 H3. apply Transpose_first with (l':=l').
  apply Transpose_sym. exact H2. apply H1. exact H0.
Qed.

Lemma Permute_trans: forall (A:Type) (l m k: list A),
  Permute l m -> Permute m k -> Permute l k.
Proof.
  intros A l m k H. generalize H k. clear k. elim H. auto.
  clear H l m. intros l l' m H0 H1 H2 H3 k H4.
  apply H1. exact H0. apply Transpose_first with (l':=m).
  exact H2. exact H4.
Qed.


Lemma Transpose_imp_eq_length: forall (A:Type)(l m:list A),
  Transpose l m -> length l = length m.
Proof.
  intros A l m H. generalize H. elim H.
  clear H l m. intros. simpl. reflexivity.
  clear H l m. intros l m l1 l2 H0 H1 H2. clear H2.
  rewrite app_length, app_length, app_length, app_length.
  rewrite H1. reflexivity. exact H0.
Qed.

Lemma Permute_imp_eq_length: forall (A:Type)(l m:list A),
  Permute l m -> length l = length m.
Proof.
  intros A l m H. generalize H. elim H.
  clear H l m. intros. reflexivity.  
  clear H l m. intros l l' m H0 H1 H2 H3. clear H3.  
  apply eq_trans with (y:=length l').
  apply H1. exact H0. apply Transpose_imp_eq_length. exact H2.
Qed.


Definition SubSet {A:Type}(l m:list A) : Prop :=
  forall (x:A), In x l -> In x m.

Definition EqSet {A:Type}(l m: list A) : Prop :=
  SubSet l m /\ SubSet m l.

Lemma SubSet_refl: forall (A:Type)(l:list A), SubSet l l.
Proof.
  intros A l. unfold SubSet. intros x. tauto.
Qed.

Lemma SubSet_trans: forall (A: Type)(l m k: list A), 
  SubSet l m -> SubSet m k -> SubSet l k.
Proof.
  intros A l m k H0 H1. unfold SubSet. intros x H2.
  apply H1. apply H0. exact H2.
Qed.


Lemma Transpose_imp_SubSet: forall (A:Type)(l m:list A),
  Transpose l m -> SubSet l m.
Proof.
  intros A l m H. generalize H. elim H.
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

Lemma Transpose_imp_EqSet: forall (A:Type)(l m:list A),
  Transpose l m -> EqSet l m.
Proof.
  intros A l m H. unfold EqSet. split. 
  apply Transpose_imp_SubSet. exact H.
  apply Transpose_imp_SubSet. apply Transpose_sym. exact H.
Qed.

Lemma Permute_imp_SubSet: forall (A:Type)(l m: list A),
  Permute l m -> SubSet l m.
Proof.
  intros A l m H. generalize H. elim H.
  clear H l m. intros. apply SubSet_refl.
  clear H l m. intros l l' m H0 H1 H2 H3. clear H3.
  apply SubSet_trans with (m:= l'). apply H1. exact H0.
  apply Transpose_imp_SubSet. exact H2.
Qed.


Lemma Permute_imp_EqSet: forall (A:Type)(l m: list A),
  Permute l m -> EqSet l m.
Proof.
  intros A l m H. unfold EqSet. split.
  apply Permute_imp_SubSet. exact H.
  apply Permute_imp_SubSet. apply Permute_sym. exact H.
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
  

Lemma Permute_cons: forall (A:Type)(l m: list A)(a: A),
  Permute l m -> Permute (a::l) (a::m).
Proof.
  intros A l m a H. generalize H. generalize a. clear a. elim H.
  clear H l m. intros. apply perm_self.
  clear H l m. intros l l' m H0 H1 H2 a H3.
  apply Permute_trans with (m:=(a::l')). apply H1. exact H0.
  apply (perm_next (a::l') (a::l') (a::m)). apply perm_self.
  apply Transpose_cons. exact H2.
Qed.



