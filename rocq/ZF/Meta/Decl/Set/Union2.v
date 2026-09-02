Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

(* union2 a b : U.                                                              *)
Definition union2 : DeclT :=
  {| paraT := [TySet; TySet]
  ;  resT  := TySet
  ;  bodyT := HoleT TySet
  |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListT
  [ (Name.local "union2", union2)
  ].

Definition env : Env := Env.union imports exports.
