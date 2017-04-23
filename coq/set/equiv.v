Set Implicit Arguments.
Require Import List.
Require Import Arith.

Require Import set.
Require Import order.
Require Import elements.
Require Import subset.

(******************************************************************************)
(*                        equiv : set -> set -> Prop                          *)
(******************************************************************************)

Definition equiv (a b:set) : Prop := (subset a b) /\ (subset b a).

(* An application of equiv *)
Lemma subset_elements : forall (a b:set), subset a b <-> 
  forall (c:set), In c (elements a) -> exists (c':set), 
    In c' (elements b) /\  equiv c c'.  
Proof.
  (* Main induction on a, additional induction on b for a = Singleton x *)
  intro a. elim a. 
  (* a = Empty *)
  intros b. split. intros H c. clear H. simpl. apply False_ind.
  intros. apply subset_0_all.
  (* a = Singleton x *)
  clear a. intro x. intro IH. clear IH. intro b. elim b. 
  (* a = Singleton x, b = Empty *)
  split. intros H. apply False_ind. apply subset_single_0 with (x:=x). exact H.
  intro H. cut(exists c':set, In c' (elements Empty) /\ equiv x c'). 
  intro H'. simpl in H'. cut False. apply False_ind. elim H'.
  intros z H''. tauto. apply H. simpl. left. reflexivity.
  (* a = Singleton x, b = Singleton y *)
  clear b. intros y H. clear H. simpl. rewrite subset_single_single. 
  split.
  intro H. intros c H'. exists y. split. left. reflexivity. elim H'. intro H''.
  rewrite <- H''. unfold equiv. exact H.  apply False_ind.
  intro H. cut(exists c' : set, (y = c' \/ False) /\ equiv x c'). intro H'.
  elim H'. intro z. intro H''. elim H''. intros H0 H1. elim H0. intro H2.
  rewrite <- H2 in H1. exact H1. apply False_ind. apply H. left. reflexivity.
  (* a = Singleton x, b = Union y z *) 
  clear b. intros y Hy z Hz. rewrite subset_single_union. simpl. split.
  intros H c H'. elim H'. intro H''. rewrite <- H''. clear H''.
  cut(subset (Singleton x) y  \/ subset (Singleton x) z).
  intro H''. elim H''.

  intro Hy'. cut(exists c':set, In c' (elements y)/\equiv x c'). intro Hy''.
  elim Hy''. intro c'. intro Hc'. exists c'. split. elim Hc'. intro Hc''.
  intro H0. clear H0. apply in_or_app. left. exact Hc''. elim Hc'. intros H0 H1. 
  exact H1. apply Hy. exact Hy'. simpl. left. reflexivity. 
  
  intro Hz'. cut(exists c':set, In c' (elements z)/\equiv x c'). intro Hz''.
  elim Hz''. intro c'. intro Hc'. exists c'. split. elim Hc'. intro Hc''. intro H0.
  clear H0. apply in_or_app. right. exact Hc''. elim Hc'. intros H0 H1. exact H1.
  apply Hz. exact Hz'. simpl. left. reflexivity. 

  exact H. apply False_ind. intro H.
  
  cut(exists c' : set, In c' (elements y ++ elements z) /\ equiv x c').
  intro H'. elim H'. intros c' Hc'. elim Hc'. intros Hc'' Hc'''.
  cut(In c' (elements y) \/ In c' (elements z)). intro H0. elim H0. 
  
  intro H1. cut(subset (Singleton x) y). intro Hy'. left. exact Hy'.

  apply Hy. intros c Hc. 
  exists c'. split. exact H1. clear H1. simpl in Hc. elim Hc.
  intro H1. rewrite <- H1. exact Hc'''. apply False_ind. 

  intro H1. cut(subset (Singleton x) z). intro Hz'. right. exact Hz'.

  apply Hz. intros c Hc. 
  exists c'. split. exact H1. clear H1. simpl in Hc. elim Hc.
  intro H1. rewrite <- H1. exact Hc'''. apply False_ind. 

  apply in_app_or.  exact Hc''. apply H. left. reflexivity. 
  
  (* a = Union x y *) 
  clear a. intros x Hx y Hy b. split. intro H.
  rewrite subset_union_all in H. intro a. intro H'. simpl in H'.
  cut(In a (elements x) \/ In a (elements y)). intro Ha. elim Ha. 

  intro Ha'. apply Hx. apply proj1 with (B:= subset y b). 
  exact H. exact Ha'. 

  intro Ha'. apply Hy.  apply proj2 with (A:= subset x b). 
  exact H. exact Ha'. 

  apply in_app_or. exact H'. intro H. rewrite subset_union_all. split. 

  apply Hx. intros a Ha. apply H. simpl. apply in_or_app. left. exact Ha.
  apply Hy. intros a Ha. apply H. simpl. apply in_or_app. right. exact Ha.
Qed.





