(* NEXT: ===> ToList                                                            *) 

Require Import Core.Set.
Require Import Core.Incl.

(* The standard mathematical notation for the singleton set.                    *)
Notation "{ x }" := (Cons x Nil) : set_scope.

Open Scope set_scope.

(* Having defined the inclusion relation <== on set, we are able to define the  *)
(* membership relation which derives from it. A set x is an element of a set y, *)
(* if and only if the singleton set {x} is a subset of y, i.e. {x} <== y.       *)
(* For some reason, Coq is not able to parse {x} <== y, so using 'incl {x} y'.  *)
Definition elem (x y:set) : Prop := incl {x} y. 

(* The membership relation is the core primitive of the language of set theory  *)
(* and deserve its own infix notation.                                          *)
Notation "x :: y" := (elem x y) : set_scope.



