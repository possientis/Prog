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
Require Import ZF.Meta.Decl.Class.Bounded.
Require Import ZF.Meta.Decl.Class.Empty.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.Empty.

(* inter A x <-> (forall y, A y -> x :< y) /\ exists y, A y.                    *)
Definition inter : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (And
          (All
            (Imp
              (App (Var 2) (Var 0))
              (Elem (Var 1) (Var 0))))
          (Ex (App (Var 2) (Var 0))))
  |}.

(* inter' A x <-> forall y, A y -> x :< y.                                      *)
Definition inter' : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (All
          (Imp
            (App (Var 2) (Var 0))
            (Elem (Var 1) (Var 0))))
  |}.

(* forall A, equiv A empty -> equiv (inter A) empty.                            *)
Definition WhenZero : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv")
        (args [Var 0; IdentT (Name.qualified "CEM" "empty") (args [])]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "inter") (args [Var 0])
          ; IdentT (Name.qualified "CEM" "empty") (args [])
          ]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* equiv (inter empty) empty.                                                   *)
Definition IsZero : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "inter")
            (args [IdentT (Name.qualified "CEM" "empty") (args [])])
        ; IdentT (Name.qualified "CEM" "empty") (args [])
        ])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A, not equiv A empty -> equiv (inter A) (inter' A).                   *)
Definition WhenNotZero : DeclP :=
  let concl :=
    Imp
      (Not
        (IdentT (Name.local "equiv")
          (args [Var 0; IdentT (Name.qualified "CEM" "empty") (args [])])))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "inter") (args [Var 0])
          ; IdentT (Name.local "inter'") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, equiv A B -> equiv (inter' A) (inter' B).                        *)
Definition EquivCompat' : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "inter'") (args [Var 1])
          ; IdentT (Name.local "inter'") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A B, equiv A B -> equiv (inter A) (inter B).                          *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "inter") (args [Var 1])
          ; IdentT (Name.local "inter") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A a, A a -> Incl (inter' A) (toClass a).                              *)
Definition IsIncl' : DeclP :=
  let concl :=
    Imp
      (App (Var 1) (Var 0))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "inter'") (args [Var 1])
          ; IdentT (Name.local "toClass") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A, not equiv A empty -> Small (inter' A).                             *)
Definition IsSmall' : DeclP :=
  let concl :=
    Imp
      (Not
        (IdentT (Name.local "equiv")
          (args [Var 0; IdentT (Name.qualified "CEM" "empty") (args [])])))
      (IdentT (Name.local "Small")
        (args [IdentT (Name.local "inter'") (args [Var 0])]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A, Small (inter A).                                                   *)
Definition IsSmall : DeclP :=
  let concl :=
    IdentT (Name.local "Small")
      (args [IdentT (Name.local "inter") (args [Var 0])])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify ZF.Meta.Decl.Axiom.Classic.exports
  ; Env.unqualify ZF.Meta.Decl.Class.Bounded.exports
  ; Env.qualifyAs "CEM" Class.Empty.exports
  ; Env.unqualify ZF.Meta.Decl.Class.Equiv.exports
  ; Env.unqualify ZF.Meta.Decl.Class.Incl.exports
  ; Env.unqualify ZF.Meta.Decl.Class.Small.exports
  ; Env.unqualify ZF.Meta.Decl.Set.Empty.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "inter" , inter)
      ; (Name.local "inter'", inter')
      ]
  ; Env.fromListP
      [ (Name.local "WhenZero"   , WhenZero)
      ; (Name.local "IsZero"     , IsZero)
      ; (Name.local "WhenNotZero", WhenNotZero)
      ; (Name.local "EquivCompat'", EquivCompat')
      ; (Name.local "EquivCompat" , EquivCompat)
      ; (Name.local "IsIncl'"     , IsIncl')
      ; (Name.local "IsSmall'"    , IsSmall')
      ; (Name.local "IsSmall"     , IsSmall)
      ]
  ].

Definition env : Env := Env.union imports exports.
