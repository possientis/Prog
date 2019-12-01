Require Import Quote.

(* 'index' defined in 'Quote' library and represents a countable variable type  *)
Inductive Formula : Set :=
| Atomic    : index -> Formula 
| Truth     : Formula
| Falsehood : Formula
| And       : Formula -> Formula -> Formula
| Or        : Formula -> Formula -> Formula
| Imp       : Formula -> Formula -> Formula
.

(* used to 'trick' the 'quote' tactic and have it leave function type unchanged *)
Definition imp (P1 P2:Prop) : Prop := P1 -> P2.

Infix "~>" := imp (no associativity, at level 95).

Definition Asgn : Type := varmap Prop.  (* 'varmap' from Quote                  *)

Fixpoint denote (atomics:Asgn) (f:Formula) : Prop :=
    match f with
    | Atomic v      => varmap_find False v atomics
    | Truth         => True
    | Falsehood     => False
    | And f1 f2     => denote atomics f1 /\ denote atomics f2
    | Or f1 f2      => denote atomics f1 \/ denote atomics f2
    | Imp f1 f2     => denote atomics f1 ~> denote atomics f2   (* '~>' !!!     *)
    end.
