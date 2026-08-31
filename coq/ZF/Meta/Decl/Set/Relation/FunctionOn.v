Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

(* FunctionOn f a : Prop.                                                       *)
Definition FunctionOn : DeclT :=
  {| paraT := [TySet; TySet];
     resT  := TyProp;
     bodyT := HoleT TyProp |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListT
  [ (Name.local "FunctionOn", FunctionOn)
  ].

Definition env : Env := Env.union imports exports.

