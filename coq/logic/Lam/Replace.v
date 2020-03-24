Require Import Eq.

Require Import Lam.T.

(* replace x by the term t                                                      *)
Definition replace' (v:Type) (e:Eq v) (x:v) (t:T v) (u:v) : T v :=
    match e u x with
    | left _    => t
    | right _   => Var u
    end.

Arguments replace' {v}.
