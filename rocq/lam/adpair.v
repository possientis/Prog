Require Import List.
Import ListNotations.

Require Import eq.
Require Import injective.
Require Import term.
Require Import free.

(* A pair of maps f,g:v-> v is an 'admissible pair' for t, if and only if they  *)
(* are inverse of each other, and they both leave free variables of t invariant *)
(* However it is sufficient to impose invariance of 'f' only                    *)
Inductive adpair (v:Type) (p:Eq v) (t:P v) (f g:v -> v) : Prop :=
| AdPair : 
    (forall x, g (f x) = x) ->
    (forall x, f (g x) = x) ->
    (forall x, In x (Fr p t) -> f x = x) ->
    adpair v p t f g.

Arguments adpair {v} _ _ _ _.

(* being an 'admissible pair for t' is a symmetric relation *)
Lemma adpair_sym : forall (v:Type) (p:Eq v) (t:P v) (f g:v -> v),
    adpair p t f g -> adpair p t g f.
Proof.
    intros v p t f g [H1 H2 H]. constructor; try (assumption).
    intros x Hx. assert (f x = x) as F. { apply H. assumption. }
    rewrite <- F at 1. apply H1.
Qed.

Lemma adpair_gf : forall (v:Type) (p:Eq v) (t:P v) (f g:v -> v) (x:v),
    adpair p t f g -> g (f x) = x.
Proof. intros v p t f g x [H _ _]. apply H. Qed.

Lemma adpair_fg : forall (v:Type) (p:Eq v) (t:P v) (f g:v -> v) (x:v),
    adpair p t f g -> f (g x) = x.
Proof. intros v p t f g x [_ H _]. apply H. Qed.



(* if (f,g) is admissible for t, then f is invariant on free variables *)
Lemma adpair_invl : forall (v:Type) (p:Eq v) (t:P v) (f g:v -> v) (x:v),
    adpair p t f g -> In x (Fr p t) -> f x = x.
Proof. intros v p t f g x [H1 H2 H] H'. apply H. assumption. Qed.

(* if (f,g) is admissible for t, then g is invariant on free variables *)
Lemma adpair_invr : forall (v:Type) (p:Eq v) (t:P v) (f g:v -> v) (x:v),
    adpair p t f g -> In x (Fr p t) -> g x = x.
Proof. 
    intros v p t f g x H H'. apply adpair_sym in H.
    apply (adpair_invl v p t g f); assumption.
Qed.

(* if (f,g) is admissible for t, then f is injective *)
Lemma adpair_injl : forall (v:Type) (p:Eq v) (t:P v) (f g:v -> v),
    adpair p t f g -> injective f.
Proof.
    intros v p t f g [H _ _] x y H'. rewrite <- (H x), <- (H y).
    rewrite H'. reflexivity.
Qed.

(* if (f,g) is admissible for t, then g is injective *)
Lemma adpair_injr : forall (v:Type) (p:Eq v) (t:P v) (f g:v -> v),
    adpair p t f g -> injective g.
Proof.
    intros v p t f g H. apply adpair_sym in H. 
    apply (adpair_injl v p t g f). assumption.
Qed.

(* if the free variables or t are free variables of t', then any    *)
(* admissible pair for t' is an admissible pair for t               *)
Lemma adpair_free : forall (v:Type) (p:Eq v) (t t':P v) (f g:v -> v),
    incl (Fr p t) (Fr p t') -> adpair p t' f g -> adpair p t f g.
Proof.
    intros v p t t' f g I [H1 H2 H]. constructor; (try assumption).
    intros x Hx. apply H. apply I. assumption.
Qed.


Lemma adpair_Appl : forall (v:Type) (p:Eq v) (t1 t2:P v) (f g:v -> v),
    adpair p (App t1 t2) f g -> adpair p t1 f g.
Proof.
    intros v p t1 t2 f g. apply adpair_free. simpl. 
    apply incl_appl. apply incl_refl.
Qed.

Lemma adpair_Appr : forall (v:Type) (p:Eq v) (t1 t2:P v) (f g:v -> v),
    adpair p (App t1 t2) f g -> adpair p t2 f g.
Proof.
    intros v p t1 t2 f g. apply adpair_free. simpl. 
    apply incl_appr. apply incl_refl.
Qed.





