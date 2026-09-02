Require Import List.
Import ListNotations.

Require Import eq.
Require Import index.


Definition vequal (v:Type) (p:Eq v) (x y:v) (lx ly:list v) : Prop :=
    match index p x lx, index p y ly with
    | Some i, Some j    => i = j
    | None  , None      => x = y
    | _     , _         => False
    end.


Arguments vequal {v} _ _ _ _ _.

