Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Class.Empty.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Small.

(* Proper P <-> not Small P.                                                    *)
Definition Proper : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyProp
  ;  bodyT := Not (IdentT (Name.local "Small") (args [Var 0]))
  |}.

(* forall A, Proper A -> not equiv A empty.                                     *)
Definition IsNotEmpty : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Proper") (args [Var 0]))
      (Not
        (IdentT (Name.local "equiv")
          (args [Var 0; IdentT (Name.local "empty") (args [])])))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Empty.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Small.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "Proper", Proper)
      ]
  ; Env.fromListP
      [ (Name.local "IsNotEmpty", IsNotEmpty)
      ]
  ].

Definition env : Env := Env.union imports exports.
