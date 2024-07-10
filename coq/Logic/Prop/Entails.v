Require Import Logic.List.In.

Require Import Logic.Prop.Syntax.
Require Import Logic.Prop.Context.
Require Import Logic.Prop.Semantics.

Declare Scope Prop_Entails_scope.

Definition Entails (v:Type)(G:Ctx v) (p:P v) : Prop := 
  forall (f:v -> bool), 
  (forall (q:P v), (q :: G) -> eval f q = true) -> eval f p = true.

Arguments Entails {v}.

Notation "G ::- p" := (Entails G p)
  (at level 90, no associativity) : Prop_Entails_scope.

Open Scope Prop_Entails_scope.
