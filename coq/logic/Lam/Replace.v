Require Import Eq.

Require Import Lam.T.

(* replace x by the term t                                                      *)
Definition replace' (v:Type) (e:Eq v) (x:v) (t:T v) (u:v) : T v :=
    match eqDec u x with
    | left _    => t
    | right _   => Var u
    end.

Arguments replace' {v} {e}.

Notation "t // x" := (replace' x t)
    (at level 70, no associativity) : BetaReplace_scope.

Open Scope BetaReplace_scope.


