Inductive pFormula : Set :=
| Top  : pFormula
| Bot  : pFormula
| Conj : pFormula -> pFormula -> pFormula
.

Fixpoint pFormulaDenote (p:pFormula) : Prop :=
    match p with
    | Top           => True
    | Bot           => False
    | Conj p1 p2    => pFormulaDenote p1 /\ pFormulaDenote p2
    end.

(*  Def: An reflexive type is an inductive type which includes at 
    least one constructor that takes as an argument a function 
    returning the same type we are defining                        *)

Inductive Formula : Set :=
| Eq     : nat -> nat -> Formula
| And    : Formula -> Formula -> Formula
| Forall : (nat -> Formula) -> Formula     (* reflexive type ! *)
.

Definition forall_refl : Formula := Forall (fun x => Eq x x). 

Fixpoint formulaDenote (p:Formula) : Prop :=
    match p with
    | Eq n m        => n = m
    | And p1 p2     => formulaDenote p1 /\ formulaDenote p2
    | Forall P      => forall (n:nat), formulaDenote (P n)
    end.

Fixpoint swapper (p:Formula) : Formula :=
    match p with 
    | Eq n m        => Eq m n 
    | And p1 p2     => And (swapper p2) (swapper p1)
    | Forall P      => Forall (fun n => swapper (P n))
    end.

Lemma swapper_preserves_truth : forall (p:Formula), 
    formulaDenote p -> formulaDenote (swapper p).
Proof.
    induction p as [n m|p1 IH1 p2 IH2|P IH]; simpl.
    - intros. symmetry. assumption.
    - intros [H1 H2]. split.
        + apply IH2. assumption.
        + apply IH1. assumption.
    - intros H n. apply IH, H.
Qed.

(*
Check Formula_ind.
*)

(* Error: Non strictly positive occurrence of "Term" 
Inductive Term : Set :=
| App : Term -> Term -> Term
| Lam : (Term -> Term) -> Term 
.

If this definition was accepted by Coq, then we could define:

Definition uhoh (t:Term) : Term :=
    match t with 
    | Abs f         => f t
    | _             => t
    end.

from which we would obtain:

uhoh (Abs uhoh) = 
uhoh (Abs uhoh) = ...
*)



