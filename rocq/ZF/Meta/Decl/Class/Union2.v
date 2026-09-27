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
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.Pair.
Require Import ZF.Meta.Decl.Set.Union.

(* union2 P Q x <-> P x \/ Q x.                                                 *)
Definition union2 : DeclT :=
  {| paraT := [TyClass; TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Or
          (App (Var 2) (Var 0))
          (App (Var 1) (Var 0)))
  |}.

(* forall P Q R S, equiv P Q -> equiv R S -> equiv (P \/ R) (Q \/ S).           *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "union2") (args [Var 3; Var 1])
            ; IdentT (Name.local "union2") (args [Var 2; Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> equiv (P \/ R) (Q \/ R).                          *)
Definition EquivCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "union2") (args [Var 2; Var 0])
          ; IdentT (Name.local "union2") (args [Var 1; Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> equiv (R \/ P) (R \/ Q).                          *)
Definition EquivCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "union2") (args [Var 0; Var 2])
          ; IdentT (Name.local "union2") (args [Var 0; Var 1])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q, Small P -> Small Q -> Small (P \/ Q).                            *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "union2") (args [Var 1; Var 0])])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify Pair.exports
  ; Env.unqualify Union.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "union2", union2)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat" , EquivCompat)
      ; (Name.local "EquivCompatL", EquivCompatL)
      ; (Name.local "EquivCompatR", EquivCompatR)
      ; (Name.local "IsSmall"     , IsSmall)
      ]
  ].

Definition env : Env := Env.union imports exports.
