Require Import Eq.

Require Import Lam.T.

(* replace x by the term t                                                      *)
Definition replaceT (v:Type) (e:Eq v) (x:v) (t:T v) (u:v) : T v :=
    match eqDec u x with
    | left _    => t
    | right _   => Var u
    end.

Arguments replaceT {v} {e}.

Notation "t // x" := (replaceT x t)
    (at level 70, no associativity) : BetaReplace_scope.

Open Scope BetaReplace_scope.


