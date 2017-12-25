Require Import Axiom_Extensionality.
Require Import Axiom_ProofIrrelevance.
Require Import Category3.

(* TODO *)

Lemma eq_Category3 : forall (c c':Category3),
    (A3 c = A3 c') -> 
    (forall f:A3 c, source3 c f = source3 c' f) ->
    (forall f:A3 c, target3 c f = target3 c' f) ->
    (forall f g:A3 c, compose3 c f g = compose3 c' f g) -> c = c'. 
