Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Set.Empty.

(* one x <-> x = empty.                                                         *)
Definition one : DeclT :=
  {| paraT := []
  ;  resT  := TyClass
  ;  bodyT := Lam (SyntaxT.Equal (Var 0) (IdentT (Name.local "empty") (args [])))
  |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unqualify Empty.exports.

Definition exports : Env := Env.fromListT
  [ (Name.local "one", one)
  ].

Definition env : Env := Env.union imports exports.
