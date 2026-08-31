Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.Relation.FunctionOn.

(* eval f a : U.                                                                *)
Definition eval : DeclT :=
  {| paraT := [TySet; TySet]
  ;  resT  := TySet
  ;  bodyT := HoleT TySet
  |}.

Definition imports : Env := Env.unions
  [ Empty.exports
  ; FunctionOn.exports
  ].

Definition exports : Env := Env.fromListT
  [ ("eval"%string, eval)
  ].

Definition env : Env := Env.union imports exports.


