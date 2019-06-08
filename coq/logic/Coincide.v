Require Import List.

(* It is not convenient in Coq to define the notion of the restriction of a     *)
(* function. However, we often need to express the fact that two functions      *)
(* coincide on a given subset. This we can do using a list instead of subset    *) 
Definition coincide (v w:Type) (xs:list v) (f g:v -> w) : Prop :=
    (forall (x:v), In x xs -> f x = g x).

Arguments coincide {v} {w} _ _ _.
