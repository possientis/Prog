Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
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

Definition evalName : Name :=
  Name.name ["Set"; "Relation"; "Eval"] "eval".

Definition imports : Env := Env.unions
  [ Empty.exports
  ; FunctionOn.exports
  ].

Definition exports : Env := Env.fromListT
  [ (evalName, eval)
  ].

Definition env : Env := Env.union imports exports.


