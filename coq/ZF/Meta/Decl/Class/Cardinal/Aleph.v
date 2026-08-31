Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

(* Aleph : Class.                                                               *)
Definition Aleph : DeclT :=
  {| paraT := []
  ;  resT  := TyClass
  ;  bodyT := HoleT TyClass
  |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListT
  [ (Name.local "Aleph", Aleph)
  ].

Definition env : Env := Env.union imports exports.
