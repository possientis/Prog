Require Import Quote.
Require Import List.
Require Import ListSet.

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

Definition Env : Type := varmap Prop.  (* 'varmap' from Quote                   *)

Definition lookup (env:Env) (k:index) : Prop := varmap_find False k env.

Fixpoint denote (env:Env) (f:Formula) : Prop :=
    match f with
    | Atomic k      => lookup env k
    | Truth         => True
    | Falsehood     => False
    | And f1 f2     => denote env f1 /\ denote env f2
    | Or f1 f2      => denote env f1 \/ denote env f2
    | Imp f1 f2     => denote env f1 ~> denote env f2   (* '~>' !!!             *)
    end.

Definition index_eq : forall (x y:index), {x = y} + {x <> y}.
    decide equality.
Defined.

Definition add (s:set index) (k:index) : set index := set_add index_eq k s.

(* giving up                                                                    *)
Definition In_dec : forall (s:set index) (k:index), {In k s} + {~In k s}.
    intros s k. revert s. refine (fix F (s : set index) : {In k s} + {~In k s}:=
        match s with
        | nil       => No
        | k' :: s'  => index_eq k' k || F s'
        end).
Show.



