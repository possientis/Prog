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

(* We cannot follow set theoretic proof as this is a stronger result, due to    *)
(* the order being preserved in lists. Structural induction on t                *)
(*
Lemma valid_free : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    valid e e' f t <-> forall (s:T v), s <<= t -> free e' (fmap f s) = map f (free e s).
Proof.
    intros v w e e' f t. split.
    - induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl; intros H s H'.
        + destruct H' as [H'|H'].
            { subst. reflexivity. }
            { inversion H'. }
        + unfold isSubFormulaOf in H'. simpl in H'.
        

Show.
*)
