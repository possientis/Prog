Require Import List.
Import ListNotations.

Require Import eq.
Require Import composition.
Require Import injective.
Require Import term.
Require Import var.
Require Import permute.
Require Import vmap.

(* syntactic sugar *)
Definition swap (v:Type) (p:Eq v) (x y:v) : P v -> P v := vmap (permute p x y).

Arguments swap {v} _ _ _ _.


Lemma swap_inj : forall (v w:Type) (p:Eq v) (q:Eq w) (x y:v) (f:v -> w) (t:P v),
    injective f -> vmap f (swap p x y t) = swap q (f x) (f y) (vmap f t).
Proof.
    intros v w p q x y f t I. unfold swap.
    rewrite <- vmap_comp. 
    rewrite (vmap_eq v w (f ; permute p x y) (permute q (f x) (f y); f)).
    - apply vmap_comp.
    - intros u Hu. apply permute_comp. assumption.
Qed.

Lemma swap_commute : forall (v:Type) (p:Eq v) (x y:v) (t:P v),
    swap p x y t = swap p y x t.
Proof.
    intros v p x y t. unfold swap. apply vmap_eq.
    intros u Hu. apply permute_commute.
Qed.


Lemma swap_involution : forall (v:Type) (p:Eq v) (x y:v) (t:P v),
    swap p x y (swap p x y t) = t.
Proof.
    intros v p x y t. unfold swap. rewrite <- vmap_comp.
    rewrite (vmap_eq v v _ id).
    - apply vmap_id.
    - intros u Hu. apply permute_involution.
Qed.

Lemma swap_thrice : forall (v:Type) (p:Eq v) (x y z:v) (t:P v),
    x <> z  ->
    y <> z  ->
    swap p x y (swap p y z (swap p x y t)) = swap p x z t.
Proof.
    intros v p x y z t Hxz Hyz. unfold swap.
    rewrite <- vmap_comp, <- vmap_comp. apply vmap_eq.
    intros u _. unfold comp. apply permute_thrice; assumption.
Qed.
