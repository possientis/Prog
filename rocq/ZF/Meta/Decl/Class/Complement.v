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

Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.

(* complement A x <-> not A x.                                                  *)
Definition complement : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyClass
  ;  bodyT := Lam (Not (App (Var 1) (Var 0)))
  |}.

(* forall A B, equiv A B -> equiv (complement A) (complement B).                *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "complement") (args [Var 1])
          ; IdentT (Name.local "complement") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, Incl B A -> Incl (complement A) (complement B).                  *)
Definition InclCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 0; Var 1]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "complement") (args [Var 1])
          ; IdentT (Name.local "complement") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Incl.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "complement", complement)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat", EquivCompat)
      ; (Name.local "InclCompat" , InclCompat)
      ]
  ].

Definition env : Env := Env.union imports exports.
