Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

(* Functional F : Prop.                                                         *)
Definition Functional : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyProp
  ;  bodyT := HoleT TyProp
  |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListT
  [ (Name.local "Functional", Functional)
  ].

Definition env : Env := Env.union imports exports.
