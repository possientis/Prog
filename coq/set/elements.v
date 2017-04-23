Set Implicit Arguments.
Require Import List.
Require Import Arith.
Require Import Arith.Max.

Require Import set.
Require Import order.

(******************************************************************************)
(*                        elements : set -> list set                          *)
(******************************************************************************)

Fixpoint elements (a:set) : list set :=
  match a with
    | Empty         => nil
    | Singleton x   => x::nil
    | Union x y     => (elements x) ++ (elements y) 
  end.

Lemma elements_order : forall (a x:set), In x (elements a) -> order x < order a.
Proof. intro a. elim a. (* induction on a*)
  (* a = Empty *)
  simpl. intro x. apply False_ind. 
  (* a = Singleton x *)
  clear a. intro x. intro H. clear H. intro z. simpl. intro H. elim H. intro H'.
  rewrite <- H'. unfold lt. apply le_n. apply False_ind. 
  (* a = Union x y *)
  clear a. intros x Hx y Hy z. simpl. intro H. 
  cut(In z (elements x) \/ In z (elements y)). intro H'. elim H'.

  intro Hx'. unfold lt. apply le_S. apply le_trans with (m:= order x). 
  apply Hx. exact Hx'. apply le_max_l.

  intro Hy'. unfold lt. apply le_S. apply le_trans with (m:= order y).
  apply Hy. exact Hy'. apply le_max_r. 

  apply in_app_or. exact H.
Qed.



