Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

(* ordPair a b : U.                                                             *)
Definition ordPair : DeclT :=
  {| paraT := [TySet; TySet]
  ;  resT  := TySet
  ;  bodyT := HoleT TySet
  |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListT
  [ (Name.local "ordPair", ordPair)
  ].

Definition env : Env := Env.union imports exports.
