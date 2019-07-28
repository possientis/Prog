Require Import List.

Require Import Eq.

Require Import Lam.T.
Require Import Lam.Free.
Require Import Lam.Subformula.

Definition valid (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v) : Prop :=
    forall (s:T v) (x:v), s <<= t -> 
        In x (free e s) -> In (f x) (free e' (fmap f s)).

Arguments valid {v} {w} _ _ _ _.

(* f is valid for t iff it is valid for every sub-term of t                     *)
Lemma valid_sub : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    valid e e' f t <-> forall (s:T v), s <<= t -> valid e e' f s.    
Proof.
    intros v w e e' f t. split.
    - intros H s H1. unfold valid. intros r x H2 H3. apply H.
        + apply Sub_tran with s; assumption.
        + assumption.
    - intros H. apply H. apply Sub_refl.
Qed.
