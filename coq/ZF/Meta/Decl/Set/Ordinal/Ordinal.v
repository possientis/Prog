Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition Ordinal : DeclT :=
  {| paraT := [TySet]
  ;  resT  := TyProp
  ;  bodyT := HoleT TyProp
  |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListT
  [ ("Ordinal"%string, Ordinal)
  ].

Definition env : Env := Env.union imports exports.
