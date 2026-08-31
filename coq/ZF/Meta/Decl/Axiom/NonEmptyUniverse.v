Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* exists x, True                                                               *)
Definition NonEmptyUniverse : DeclT :=
  {| paraT := []
  ;  resT  := TyProp
  ;  bodyT := Ex VarTySet Top
  |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListT
  [ ("NonEmptyUniverse"%string, NonEmptyUniverse)
  ].

Definition env : Env := Env.union imports exports.
