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
Require Import ZF.Meta.Decl.Class.Empty.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Small.

(* truncate A x <-> Small A /\ A x.                                             *)
Definition truncate : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (And
          (IdentT (Name.local "Small") (args [Var 1]))
          (App (Var 1) (Var 0)))
  |}.

(* forall A B, equiv A B -> equiv (truncate A) (truncate B).                    *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "truncate") (args [Var 1])
          ; IdentT (Name.local "truncate") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A, Small A -> equiv (truncate A) A.                                   *)
Definition WhenSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 0]))
      (IdentT (Name.local "equiv")
        (args [IdentT (Name.local "truncate") (args [Var 0]); Var 0]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A, not Small A -> equiv (truncate A) empty.                           *)
Definition WhenNotSmall : DeclP :=
  let concl :=
    Imp
      (Not (IdentT (Name.local "Small") (args [Var 0])))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "truncate") (args [Var 0])
          ; IdentT (Name.local "empty") (args [])
          ]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A, Small (truncate A).                                                *)
Definition IsSmall : DeclP :=
  let concl :=
    IdentT (Name.local "Small")
      (args [IdentT (Name.local "truncate") (args [Var 0])])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Classic.exports
  ; Env.unqualify Empty.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Small.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "truncate", truncate)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat" , EquivCompat)
      ; (Name.local "WhenSmall"   , WhenSmall)
      ; (Name.local "WhenNotSmall", WhenNotSmall)
      ; (Name.local "IsSmall"     , IsSmall)
      ]
  ].

Definition env : Env := Env.union imports exports.
