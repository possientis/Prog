Require Import List.
Import ListNotations.

Require Import Logic.Class.Eq.

Require Import Logic.List.In.
Require Import Logic.List.Include.
Require Import Logic.List.Intersect.
Require Import Logic.List.Difference.

Require Import Logic.Fol.Dmap.
Require Import Logic.Fol.Free.
Require Import Logic.Fol.Bound.
Require Import Logic.Fol.Valid.
Require Import Logic.Fol.Syntax.
Require Import Logic.Fol.Functor.

(*
Lemma localInv_lemma : 
    forall (v w:Type)(e:Eq v)(e':Eq w)(f:v -> w)(v0 v1:list v)(g0 g1:w -> v),
        forall (xs:list v) (p:P v), 
            (forall (x:v), (x :: v0) -> g0 (f x) = x)   ->
            (forall (x:v), (x :: v1) -> g1 (f x) = x)   ->
            (bnd p ++ xs <= v0)                         ->
            (Fr p  \\ xs <= v1)                         -> 
            valid f p                                   ->
            (map f xs /\ map f (Fr p \\ xs)) = []       ->
                dmap_ g0 g1 (map f xs) (fmap f p) = p.
Proof.

Show.
*)
