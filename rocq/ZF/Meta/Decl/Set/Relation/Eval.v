Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.Relation.FunctionOn.

(* eval f a : U.                                                                *)
Definition eval : DeclT :=
  {| paraT := [TySet; TySet]
  ;  resT  := TySet
  ;  bodyT := HoleT TySet
  |}.

Definition imports : Env := Env.unions
  [ Env.unqualify Empty.exports
  ; Env.unqualify FunctionOn.exports
  ].

Definition exports : Env := Env.fromListT
  [ (Name.local "eval", eval)
  ].

Definition env : Env := Env.union imports exports.


