Require Import List.
Import ListNotations.

Require Import eq.
Require Import identity.
Require Import composition.
Require Import term.
Require Import var.

(* will turn 'P' into a functor *)
Fixpoint vmap (v w:Type) (f:v -> w) (t:P v) : P w :=
    match t with
    | Var x     => Var (f x)
    | App t1 t2 => App (vmap v w f t1) (vmap v w f t2)
    | Lam x t1  => Lam (f x) (vmap v w f t1)
    end.

Arguments vmap {v} {w} _ _.

Lemma vmap_id : forall (v:Type) (t:P v), vmap id t = t. 
Proof.
    intros v t. induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - reflexivity.
    - rewrite IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity. 
Qed.

Open Scope composition.

Lemma vmap_comp : forall (v w u:Type) (f:v -> w) (g:w -> u) (t:P v),
    vmap (g ; f) t = vmap g (vmap f t).
Proof.
    intros v w u f g t. induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - reflexivity.
    - rewrite IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.

(* if two functions f and g coincide on the variables of a term t   *)
(* then the terms 'f t' and 'g t' coincide.                         *)
Lemma vmap_eq : forall (v w:Type) (f g:v -> w) (t:P v),
    (forall x, In x (Vr t) -> f x = g x) -> vmap f t = vmap g t.
Proof.
    intros v w f g t. induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros H.
    - simpl. simpl in H. rewrite H.
        + reflexivity.
        + left. reflexivity.
    - simpl. rewrite IH1, IH2.
        + reflexivity.
        +  intros x Hx. apply H. simpl. apply in_or_app. right. assumption.
        +  intros x Hx. apply H. simpl. apply in_or_app. left. assumption.
    - simpl. rewrite H, IH1.
        + reflexivity.
        + intros y Hy. apply H. right. assumption.
        + left. reflexivity.
Qed.

