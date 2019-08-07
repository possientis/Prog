Require Import List.

Require Import Eq.
Require Import Remove.

Require Import Fol.P.
Require Import Fol.Free.
Require Import Fol.Subformula.

Definition valid (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (q:P v) : Prop :=
    forall (p:P v) (x:v), p <<= q -> 
        In x (free e p) -> In (f x) (free e' (fmap f p)).

Arguments valid {v} {w} _ _ _ _.

(* f is valid for q iff it is valid for every sub-formula of q                  *)
Lemma valid_sub : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (q:P v),
    valid e e' f q <-> forall (p:P v), p <<= q -> valid e e' f p.    
Proof.
    intros v w e e' f q. split.
    - intros H p H1. unfold valid. intros o x H2 H3. apply H.
        + apply Sub_tran with p; assumption.
        + assumption.
    - intros H. apply H. apply Sub_refl.
Qed.
