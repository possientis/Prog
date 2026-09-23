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

Require Import ZF.Meta.Decl.Axiom.Classic.
Require Import ZF.Meta.Decl.Axiom.NonEmptyUniverse.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.Specify.

(* empty x <-> False.                                                           *)
Definition empty : DeclT :=
  {| paraT := []
  ;  resT  := TyClass
  ;  bodyT := Lam Bot
  |}.

(* forall x, empty x <-> False.                                                 *)
Definition Charac : DeclP :=
  let concl :=
    All
      (Iff
        (App (IdentT (Name.local "empty") (args [])) (Var 0))
        Bot)
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Small empty.                                                                 *)
Definition IsSmall : DeclP :=
  let concl :=
    IdentT (Name.local "Small")
      (args [IdentT (Name.local "empty") (args [])])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A, not equiv A empty iff exists x, A x.                               *)
Definition HasElem : DeclP :=
  let concl :=
    Iff
      (Not
        (IdentT (Name.local "equiv")
          (args [Var 0; IdentT (Name.local "empty") (args [])])))
      (Ex (App (Var 1) (Var 0)))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A, equiv A empty iff not exists x, A x.                               *)
Definition HasNoElem : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.local "equiv")
        (args [Var 0; IdentT (Name.local "empty") (args [])]))
      (Not (Ex (App (Var 1) (Var 0))))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, equiv A empty -> equiv (image F A) empty.                        *)
Definition ImageOf : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv")
        (args [Var 0; IdentT (Name.local "empty") (args [])]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "image") (args [Var 1; Var 0])
          ; IdentT (Name.local "empty") (args [])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, Incl A B -> equiv B empty -> equiv A empty.                      *)
Definition WhenIncl : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "equiv")
          (args [Var 0; IdentT (Name.local "empty") (args [])]))
        (IdentT (Name.local "equiv")
          (args [Var 1; IdentT (Name.local "empty") (args [])])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Classic.exports
  ; Env.unqualify NonEmptyUniverse.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify Specify.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "empty", empty)
      ]
  ; Env.fromListP
      [ (Name.local "Charac"   , Charac)
      ; (Name.local "IsSmall"  , IsSmall)
      ; (Name.local "HasElem"  , HasElem)
      ; (Name.local "HasNoElem", HasNoElem)
      ; (Name.local "ImageOf"  , ImageOf)
      ; (Name.local "WhenIncl" , WhenIncl)
      ]
  ].

Definition env : Env := Env.union imports exports.
