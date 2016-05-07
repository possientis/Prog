Require Import List.

(* inductive predicate expressing the fact that two lists are obtained from
each other, by the permutation of two consecutive elements  *)
Inductive transposition {A:Type} : list A -> list A -> Prop :=
  | transp_pair : forall(x y:A), transposition (x::y::nil) (y::x::nil)
  | transp_gen  : forall (l m l1 l2 : list A), 
    transposition l m -> transposition (l1++l++l2) (l1++m++l2).

(* one common issue with this sort of definition is that constructors of the
inductive predicates are akin to 'axioms', and it is very easy to define the
wrong thing, or things that are inconsistent, or incomplete etc *)

(* Here is another way to go about it *)
Definition transposition' {A:Type} (l: list A) (m:list A) : Prop := 
  exists (l1 l2:list A) (x y:A), 
  l = l1++(x::y::nil)++l2 /\ m = l1++(y::x::nil)++l2.

(* just in case, this may allow use to use 'auto with transp_base' *)
Hint Resolve transp_pair transp_gen : transp_base.

(* ideally, you want to check the equivalence between the two notions *)
Lemma tranposition_check: forall (A:Type)(l m:list A),
  transposition l m <-> transposition' l m.
Proof.
  intros A l m. split. intro H. generalize H. elim H. intros. 
  unfold transposition'. exists nil, nil, x, y. auto.
  clear H l m. intros l m l1 l2 H0 H1 H2. clear H2.
  cut (transposition' l m). clear H0 H1. intro H.
  unfold transposition' in H. elim H. intro l3. clear H. intro H.
  elim H. intro l4. clear H. intro H. 
  elim H. intro x. clear H. intro H.
  elim H. intro y. clear H. intro H.
  elim H. clear H. intros H0 H1.
  unfold transposition'.
  exists (l1++l3), (l4++l2), x, y. rewrite H0, H1. clear H0 H1.
  split. rewrite <- app_assoc with (l:=l1). rewrite <- app_assoc with (l:=l3).
  rewrite <- app_assoc with (n:=l2). reflexivity. 
  rewrite <- app_assoc with (l:=l1). rewrite <- app_assoc with (l:=l3).
  rewrite <- app_assoc with (n:=l2). reflexivity.
  apply H1. exact H0.
  intro H. unfold transposition' in H. elim H. clear H. intros l1 H.
  elim H. clear H. intros l2 H. elim H. clear H. intros x H.
  elim H. clear H. intros y H. elim H. clear H. intros Hl Hm.
  rewrite Hl, Hm. apply transp_gen. apply transp_pair.
Qed.

(* This inductive predicate expresses the fact that two 
lists are permutations of one another *)
Inductive permutation {A:Type} : list A -> list A -> Prop :=
  | perm_zero : forall l:list A, permutation l l
  | perm_next : forall l l' m: list A, 
    permutation l l' -> transposition l' m -> permutation l m. 


Lemma permutation_reflexive : forall (A:Type) (l:list A), permutation l l.
Proof.
  intros A l. apply perm_zero.
Qed.

 
Lemma transposition_symmetric: forall (A:Type) (l m: list A),
  transposition l m -> transposition m l.
Proof.
  intros A l m H. generalize H. elim H. clear l m H.
  intros x y H. clear H. apply transp_pair. clear l m H.
  intros l m l1 l2 H H' H0. clear H0. apply transp_gen.
  apply H'. exact H.
Qed.

Lemma transposition_first: forall (A:Type) (l l' m:list A),
  transposition l l' -> permutation l' m -> permutation l m.
Proof.
  intros A l l' m H0 H1. generalize H0. clear H0. generalize H1 l. 
  elim H1. clear H1 l l' m. intros m. intro H. clear H. intro l.
  intro H. apply perm_next with (l':=l). apply perm_zero. exact H.
  clear H1 l l' m. intros l l' m H0 H1 H3 H4 k H5.
  eapply perm_next. apply H1. exact H0. exact H5. exact H3.
  (* dont understand why normal 'apply ... with' was failing *)
Qed.

Lemma permutation_symmetric: forall (A:Type) (l m: list A),
  permutation l m -> permutation m l.
Proof.
  intros A l m H. generalize H. elim H. auto. clear H m l.  
  intros l l' m H0 H1 H2 H3. apply transposition_first with (l':=l').
  apply transposition_symmetric. exact H2. apply H1. exact H0.
Qed.
