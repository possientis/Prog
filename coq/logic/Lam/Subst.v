Require Import List.
Import ListNotations.

Require Import Eq.

Require Import Lam.T.

(* This module has no equivalent in Fol                                         *)

(* xs represents the list of variables which are deemed 'bound'                 *)
Definition h_ (v:Type) (e:Eq v) (f:v -> T v) (xs : list v) (x:v) : T v :=
    match in_dec e x xs with
    | left _    => Var x        (* x is deemed bound    -> Var x                *)
    | right _   => f x          (* x is deemed free     -> f x                  *)
    end.

Arguments h_ {v}.

(* Formally similar to the definition of dmap                                   *)
Fixpoint subst_ (v:Type) (e:Eq v) (f:v -> T v) (t:T v) (xs:list v) : T v :=
    match t with
    | Var x     => h_ e f xs x
    | App t1 t2 => App (subst_ v e f t1 xs) (subst_ v e f t2 xs)
    | Lam x t1  => Lam x (subst_ v e f t1 (x :: xs))        (* x now bound      *)
    end.

Arguments subst_ {v}.


Definition subst (v:Type) (e:Eq v) (f:v -> T v) (t:T v) : T v :=
    subst_ e f t [].

Arguments subst {v}.
