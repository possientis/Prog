Require Import List.
Import ListNotations.

Require Import eq.
Require Import injective.
Require Import incl.
Require Import term.
Require Import var.
Require Import inj_on_list.
Require Import permute.
Require Import inj_on_term.
Require Import remove.
Require Import vmap.
Require Import swap.



(* Returns the list of free variables (with possible duplication) in a term     *)
(* When facing a lambda abstraction, we need to be able to remove a variable    *)
(* from the list of free variables of the subterm, hence decidable equality.    *)
Fixpoint Fr (v:Type) (p:Eq v) (t:P v) : list v :=
    match t with
    | Var x         => [x]
    | App t1 t2     => Fr v p t1 ++ Fr v p t2
    | Lam x t1      => remove p x (Fr v p t1)
    end.


Arguments Fr {v} _ _.


(* A free variable of a term is also a variable *)
Lemma free_is_var : forall (v:Type) (p:Eq v) (t:P v), incl (Fr p t) (Vr t).
Proof.
    intros v p t. induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - apply incl_refl.
    - apply incl_app2; assumption.
    - apply incl_tran with (remove p x (Vr t1)).
        + apply remove_mon. { assumption. }
        + apply incl_tran with (Vr t1).
            { apply remove_incl. }
            { apply incl_tl. apply incl_refl. }
Qed.

(* The free variables of 'f t' are images by 'f' of free variables of 't'   *)
Lemma free_vmap : forall (v w:Type) (p:Eq v) (q:Eq w) (f:v -> w) (t:P v),
    incl (Fr q (vmap f t)) (map f (Fr p t)).
Proof.
    intros v w p q f t. induction t; simpl.
    - apply incl_refl.
    - rewrite map_app. apply incl_app2; assumption.
    - apply incl_tran with (remove q (f v0) (map f (Fr p t))).
        + apply remove_mon. assumption.
        + apply remove_map.
Qed.


(* if f is injective on the term t, then the free variables of 'f t'        *)
(* are exactly the images by f of the free variables of 't'                 *) 
Lemma free_vmap_inj : forall (v w:Type) (p:Eq v) (q:Eq w) (f:v -> w) (t:P v),
    injective_on_term t f -> Fr q (vmap f t) = map f (Fr p t).
Proof.
    intros v w p q f t. 
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl; intros H.
    - reflexivity.
    - rewrite map_app,IH1, IH2. reflexivity.
        + apply injective_on_term_Appr with t1. assumption.
        + apply injective_on_term_Appl with t2. assumption.
    - rewrite IH1. apply remove_inj2.
        { apply injective_incl with (x :: Vr t1).
            { apply incl_cons2. apply free_is_var. }
            { assumption. }
        }
        { apply injective_incl with (x :: Vr t1). 
            { apply incl_tl. apply incl_refl. }
            { assumption. }
        }
Qed.


Lemma free_permute : forall (v:Type) (p:Eq v) (x y:v) (t:P v),
    Fr p (swap p x y t) = map (permute p x y) (Fr p t).
Proof.
    intros v p x y t. unfold swap.
    apply free_vmap_inj.
    apply inj_is_inj_on_list. apply permute_injective.
Qed.


Lemma free_swap : forall (v:Type) (p:Eq v) (x y:v) (t:P v),
   ~In y (Fr p t)  <-> ~In x (Fr p (swap p x y t)).
Proof.
    intros v p x y t. split; intros H.
    - rewrite free_permute. rewrite <- (permute_y v p x y) at 1.
      apply injective_not_in.
      + apply inj_is_inj_on_list. apply permute_injective.
      + assumption.
    - rewrite <- (swap_involution v p x y t). rewrite free_permute.
      rewrite <- (permute_x v p x y) at 1. 
      apply injective_not_in.
      + apply inj_is_inj_on_list. apply permute_injective.
      + assumption.
Qed.



