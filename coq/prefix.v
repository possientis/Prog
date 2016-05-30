Require Import List.

Section prefix.


Variable A:Type.

(*
Implicit Types (l m: list A).
*)

(* this file is about the study of the binary relation prefix on lists *)
(* Spefically this relation is defined and shown to be a partial order  *)

(* one possible definition as an inductive predicate *)
Inductive prefix : list A -> list A -> Prop :=
  | prefixNil: forall (l: list A), prefix nil l
  | prefixCons: forall (a: A)(l m:list A), prefix l m -> prefix (a::l) (a::m). 

(* another possible definition as an inductive predicate *)
Inductive prefix': list A -> list A -> Prop :=
  | prefixEq': forall (l:list A), prefix' l l
  | prefixApp': forall (l m k:list A), prefix' l m -> prefix' l (m++k).

(* These two definition are equivalent: see Theorem prefix_is_prefix' below *)
(* A few lemmas to show the equivalence between these two definitions *)

Lemma prefixCons': forall (a:A)(l m:list A), prefix' l m -> prefix' (a::l) (a::m).
Proof.
  intros a l m H. generalize a. clear a. generalize H. elim H.
  clear l m H. intros l H a. apply prefixEq'.
  clear l m H. intros l m k H0 H1 H2 a. rewrite app_comm_cons. 
  apply prefixApp'. apply H1. exact H0.
Qed.

Lemma prefix_imp_prefix': forall (l m:list A),
  prefix l m -> prefix' l m.
Proof.
  intros l m H. generalize H. elim H.

  clear l m H. intros l H. clear H. 
  rewrite <- app_nil_l. apply prefixApp'. apply prefixEq'.

  clear l m H. intros a l m H0 H1 H2. apply prefixCons'.
  apply H1. exact H0.
Qed.

Lemma prefixEq: forall (l: list A), prefix l l.
Proof.
  intro l. elim l.
  clear l. apply prefixNil.
  clear l. intros a l H. apply prefixCons. exact H.
Qed.

Lemma prefixApp: forall (l m k:list A), prefix l m -> prefix l (m++k).
Proof.
  intros l m k H. generalize k. clear k. generalize H. elim H.
  clear l m H. intros l H0 H1. apply prefixNil.
  clear l m H. intros a l m H0 H1 H2 k. rewrite <- app_comm_cons.
  apply prefixCons. apply H1. exact H0.
Qed.

Lemma prefix'_imp_prefix: forall (l m:list A),
  prefix' l m -> prefix l m.
Proof.
  intros l m H. generalize H. elim H.
  clear l m H. intros l H. clear H. apply prefixEq.
  clear l m H. intros l m k H0 H1 H2.
  apply prefixApp. apply H1. exact H0.
Qed.

Theorem prefix_is_prefix': forall (l m:list A),
  prefix l m <-> prefix' l m.
Proof.
  intros l m. split. apply prefix_imp_prefix'. apply prefix'_imp_prefix.
Qed.


(* the relation is reflexive *) (* renaming of lemma prefixEq above *)
Lemma prefix_refl: forall (l: list A), prefix l l.
Proof.
  intros l. apply prefixEq.
Qed.

Lemma prefix_l_nil: forall (l:list A), 
  prefix l nil -> l = nil.
Proof.
  cut (forall l m:list A, prefix l m -> m = nil -> l = nil). eauto.
  intros l m H. generalize H. elim H.
  clear l m H. intros. auto.
  clear l m H. intros. discriminate.
Qed.

Lemma prefix_cons_same_head: forall (a b:A)(l m:list A),
  prefix (a::l) (b::m) -> a = b.
Proof.
  cut (forall (l' m':list A)(a b:A)(l m:list A), prefix l' m' -> 
    l' = a::l -> m' = b::m -> a = b). eauto.
  intros l m a b l' m' H. generalize a b l' m' H. clear a b m' l'. elim H.
  clear l m H. intros. discriminate.
  clear l m H. intros c l m H0 H1 a b l' m' H2 H3 H4.
  injection H3. injection H4. clear H0 H1 H2 H3 H4. intros H0 H1 H2 H3.
  rewrite H3 in H1. exact H1.
Qed.

Lemma prefix_cons_prefix_tail: forall (a b:A)(l m:list A),
  prefix (a::l) (b::m) -> prefix l m.
Proof.
  cut(forall (l' m':list A)(a b:A)(l m:list A), prefix l' m' ->
    l' = a::l -> m' = b::m -> prefix l m). eauto.
  intros l m a b l' m' H. generalize a b l' m'. clear a b l' m'. 
  generalize H. elim H.
  clear l m H. intros. discriminate.
  clear l m H. intros c l m H0 H1 H2 a b l' m' H3 H4. clear H1 H2.
  injection H3. injection H4. clear H3 H4. intros H1 H2 H3 H4.
  rewrite <- H1, <- H3. exact H0.
Qed.


(* the relation is anti-symmetric *)
Lemma prefix_anti: forall (l m:list A),
  prefix l m -> prefix m l -> l = m.
Proof.
  intros l. elim l.
  clear l. intros m H0 H1. clear H0. symmetry. apply prefix_l_nil. exact H1.
  clear l. intros a l IH m. elim m.
  clear m. intros H0 H1. clear H1. apply prefix_l_nil in H0. discriminate.
  clear m. intros b m IH' H0 H1. 
  rewrite <- prefix_cons_same_head with (a:=a)(b:=b)(l:=l)(m:=m).
  rewrite <- (IH m). reflexivity.
  apply prefix_cons_prefix_tail with (a:=a)(b:=b). exact H0.
  apply prefix_cons_prefix_tail with (a:=b)(b:=a). exact H1. exact H0.
Qed.


Lemma prefix_trans: forall (l m k: list A),
  prefix l m -> prefix m k -> prefix l k.
Proof.
  intros l m k H. generalize k. clear k. generalize H. elim H.
  clear l m H. intros. apply prefixNil.
  clear l m H. intros a l m H0 H1 H2 k. clear H2. elim k.
  clear k. intro H2. apply prefix_l_nil in H2. discriminate.
  clear k. intros b k H2 H3. 
  rewrite <- (prefix_cons_same_head a b m k). apply prefixCons.
  apply H1. exact H0. apply (prefix_cons_prefix_tail a b). exact H3.
  exact H3.
Qed.

(* Of course inductive predicates cannot be trusted              *)
(* can we define a function isPrefixOf: list A -> list A -> bool *)
(* such that isPrefixOf l m = true <-> prefix l m                *)

Section prefix_bool.
Hypothesis  A_dec: forall (x y:A), {x = y} + {x <> y}.


Fixpoint isPrefixOf (l m:list A): bool :=
  match l with
    | nil     => true
    | (a::l') => match m with
                  | nil     => false
                  | (b::m') => match A_dec a b with
                                | left  _ => isPrefixOf l' m'
                                | right _ => false
                              end
                end
  end.
(* Print Assumptions isPrefixOf. *)

Lemma isPrefixOf_cons_same_head:
  forall (a b:A)(l m:list A), isPrefixOf (a::l) (b::m) = true -> a = b.
Proof.
  intros a b l m. simpl. case (A_dec a b); intros; auto; discriminate.
Qed.

Lemma isPrefixOf_cons_isPrefixOf_tail:
  forall (a b:A)(l m:list A), 
    isPrefixOf (a::l) (b::m) = true -> isPrefixOf l m = true.
Proof.
  intros a b l m. simpl. case (A_dec a b); intros; auto; discriminate.
Qed.

Theorem prefixValidate: forall (l m:list A),
  prefix l m <-> isPrefixOf l m = true.
Proof.
  intros l m. split. 
  (* -> *)
  intro H. generalize H. elim H.
  clear l m H. simpl. intros. auto.
  clear l m H. intros a l m H0 H1 H2. simpl. case (A_dec a a).
  intro H3. clear H3. apply H1. exact H0.
  intros. auto.
  (* <- *)
  generalize m. clear m. elim l.
  intros. apply prefixNil.
  clear l. intros a l IH m. generalize a. clear a. elim m.
  clear m. simpl. intros. discriminate.
  clear m. intros b m IH' a H.
  rewrite <- (isPrefixOf_cons_same_head a b l m).
  apply prefixCons. apply IH.
  apply (isPrefixOf_cons_isPrefixOf_tail a b). exact H. exact H.
Qed.

End prefix_bool.

Lemma nat_dec: forall (n m:nat), {n = m} + {n <> m}.
Proof.
  intros n. elim n.
  clear n. intro m. elim m.
  auto. auto.
  clear n. intros n IH m. elim m.
  auto. clear m. intros m H0.
  case (IH m). clear IH. intros E. left.
  rewrite E. reflexivity. clear IH. intro E. right.
  unfold not. intro E'. injection E'. exact E.
Qed.


(* In fact, we do not need to use the bool data type in order to validate prefix *)
Fixpoint prefix'' (l m:list A): Prop :=
  match l with
    | nil     => True
    | (a::l') => match m with
                  | nil     => False
                  | (b::m') => (a=b)/\ (prefix'' l' m')
                end
  end.

Lemma prefixNil'': forall (l:list A), prefix'' nil l.
Proof.
  intros l. simpl. auto.
Qed.

Lemma prefixCons'': forall (a:A) (l m:list A),
  prefix'' l m -> prefix'' (a::l) (a::m).
Proof.
  intros a l m H. simpl. auto.
Qed.

Lemma prefix_imp_prefix'' : forall (l m: list A), 
  prefix l m -> prefix'' l m.
Proof.
  intros l m H. generalize H. elim H.
  clear H l m. intros. apply prefixNil''.
  clear H l m. intros a l m H0 H1 H2. clear H2.
  apply prefixCons''. apply H1. exact H0.
Qed.


Lemma prefix''_imp_prefix: forall (l m: list A),
  prefix'' l m -> prefix l m.
Proof.
  intros l. elim l.
  clear l. intros. apply prefixNil.
  clear l. intros a l IH. intros m. elim m.
  clear m. simpl. apply False_ind.
  clear m. intros b m IH' H. clear IH'. simpl in H. elim H. clear H.
  intros H0 H1. rewrite <- H0. apply prefixCons. apply IH. exact H1.
Qed.

Theorem prefix_is_prefix'': forall (l m:list A), 
  prefix l m <-> prefix'' l m.
Proof.
  intros l m. split. apply prefix_imp_prefix''. apply prefix''_imp_prefix.
Qed.


End prefix.

(*
Eval compute in isPrefixOf nat nat_dec (0::1::nil) (0::1::2::nil).
*)

