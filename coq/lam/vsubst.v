Require Import eq.
Require Import term.

(* defines a map v -> v which permutes x and y                      *)
Definition permute (v:Type) (p:Eq v) (x y:v) (u:v) : v :=
    match p u x with
    | left  _       => y        (* if u = x return y    *)
    | right _       =>
        match p u y with
        | left  _   => x        (* if u = y return x    *)
        | right _   => u        (* otherwise return u   *)
        end
     end.

Arguments permute {v} _ _ _.

Fixpoint vsubst (v w:Type) (f:v -> w) (t:P v) : P w :=
    match t with
    | Var x     => Var (f x)
    | App t1 t2 => App (vsubst v w f t1) (vsubst v w f t2)
    | Lam x t1  => Lam (f x) (vsubst v w f t1)
    end.

Arguments vsubst {v} {w} _ _.

Definition swap (v:Type) (p:Eq v) (x y:v) : P v -> P v := vsubst (permute p x y).

Arguments swap {v} _ _ _ _.


