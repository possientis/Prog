Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Class.Empty.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Class.Truncate.
Require Import ZF.Meta.Decl.Set.Empty.

(* truncate A := fromClass (class-truncate A).                                  *)
Definition truncate : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TySet
  ;  bodyT := FromC (IdentT (Name.qualified "CTR" "truncate") (args [Var 0]))
  |}.

(* forall A x, x belongs to truncate A iff A is small and A x.                  *)
Definition Charac : DeclP :=
  let concl :=
    Iff
      (Elem (Var 0) (IdentT (Name.local "truncate") (args [Var 1])))
      (And
        (IdentT (Name.local "Small") (args [Var 1]))
        (App (Var 1) (Var 0)))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, equivalent classes have equal truncations.                       *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (SyntaxT.Equal
        (IdentT (Name.local "truncate") (args [Var 1]))
        (IdentT (Name.local "truncate") (args [Var 0])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A, Small A -> toClass (truncate A) is equivalent to A.                *)
Definition WhenSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "toClass")
              (args [IdentT (Name.local "truncate") (args [Var 0])])
          ; Var 0
          ]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A, not Small A -> truncate A = empty.                                 *)
Definition WhenNotSmall : DeclP :=
  let concl :=
    Imp
      (Not (IdentT (Name.local "Small") (args [Var 0])))
      (SyntaxT.Equal
        (IdentT (Name.local "truncate") (args [Var 0]))
        (IdentT (Name.local "empty") (args [])))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A, equiv A empty -> truncate A = empty.                               *)
Definition WhenZero : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv")
        (args [Var 0; IdentT (Name.qualified "CEM" "empty") (args [])]))
      (SyntaxT.Equal
        (IdentT (Name.local "truncate") (args [Var 0]))
        (IdentT (Name.local "empty") (args [])))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, A included in B makes toClass (truncate A) included in B.        *)
Definition IsIncl : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "toClass")
              (args [IdentT (Name.local "truncate") (args [Var 1])])
          ; Var 0
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.qualifyAs "CEM" Class.Empty.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Small.exports
  ; Env.qualifyAs "CTR" Truncate.exports
  ; Env.unqualify Empty.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "truncate", truncate)
      ]
  ; Env.fromListP
      [ (Name.local "Charac"       , Charac)
      ; (Name.local "EquivCompat"  , EquivCompat)
      ; (Name.local "WhenSmall"    , WhenSmall)
      ; (Name.local "WhenNotSmall" , WhenNotSmall)
      ; (Name.local "WhenZero"     , WhenZero)
      ; (Name.local "IsIncl"       , IsIncl)
      ]
  ].

Definition env : Env := Env.union imports exports.
