Require Import List.
Import ListNotations.

Require Import eq.
Require Import term.



(* Given a map f:v -> P v and a lambda term t. We want to define a term     *)
(* t* where all its variables x have been substituted by the corresponding  *)
(* term f x. We are doing this in two stages: we first define a map which   *)
(* takes a list of variables as argument indicating which variables are     *)
(* bound (i.e. are not meant to be changed). The second stage consists in   *)
(* calling this function with the empty list. Note that we need the type v  *)
(* to have decidable equality. Contrary to typical textbook presentation,   *)
(* this substitution mapping does not carry out variable renaming in order  *)
(* to avoid variable capture. The upside is the relative simplicity of its  *)
(* definition, as well as the fact that it is completely decoupled from the *)
(* notion of alpha-equivalence. The downside is that variable capture may   *)
(* occur, which means that not every mapping f:v -> P v is 'valid' for t.   *)
(* However, it is possible to find a term t' which is alpha-equivalent to t *)
(* and such that f:v -> P v is 'valid' for t'.                              *)

Fixpoint subst_ (v:Type) (p:Eq v) (f:v -> P v) (t:P v) (l:list v) : P v :=
    match t with
    | Var x         => 
        match in_dec p x l with  (* testing whether x is in l         *)
        | left  _   => Var x     (* if x is in l then no substitution *)
        | right _   => f x       (* otherwise replace var x by f x    *)
        end
    | App t1 t2     => App (subst_ v p f t1 l) (subst_ v p f t2 l)
    | Lam x t1      => Lam x (subst_ v p f t1 (x :: l))
    end.

Arguments subst_ {v} _ _ _ _.


Definition subst (v:Type) (p:Eq v) (f:v -> P v) (t:P v) : P v := subst_ p f t [].

Arguments subst {v} _ _ _.


