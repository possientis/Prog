Require Import List.
Import ListNotations.

Require Import eq.
Require Import index.
Require Import vequal.
Require Import term.
Require Import alpha.

Inductive alpha_ (v:Type) (p:Eq v) : P v -> P v -> list v -> list v -> Prop :=
| BVar : forall (x y:v) (lx ly:list v), 
    vequal p x y lx ly ->
    alpha_ v p (Var x) (Var y) lx ly
| BApp : forall (t1 t1' t2 t2':P v) (l l':list v),
    alpha_ v p t1 t1' l l' ->
    alpha_ v p t2 t2' l l' ->
    alpha_ v p (App t1 t2) (App t1' t2') l l'
| ALam : forall (x y:v) (t1 t1':P v) (l l':list v),
    alpha_ v p t1 t1' (x :: l) (y :: l') ->
    alpha_ v p (Lam x t1) (Lam y t1') l l'
.

Arguments alpha_ {v} _ _ _ _ _.

Definition alpha' (v:Type) (p:Eq v) (t t':P v) : Prop := alpha_ p t t' [] [].

Arguments alpha' {v} _ _ _.

(*
Lemma alpha_cons : forall (v:Type) (p:Eq v) (x:v) (t t':P v) (l l':list v),
    alpha_ p t t' l l' <-> alpha_ p t t' (x :: l) (x :: l').
Proof.
    intros v p x t t' l l'. split; intros H.
    - revert x. induction H.
        + intros z. constructor.

Show.
*)
    
(*
Lemma alpha_alpha' : forall (v:Type) (p:Eq v) (t t':P v),
    alpha p t t' -> alpha' p t t'.
Proof.
    intros v p t t' H. unfold alpha'. induction H.
    - constructor. unfold vequal. simpl. reflexivity.
    - constructor; assumption.
    - constructor. 


Show.
*)
