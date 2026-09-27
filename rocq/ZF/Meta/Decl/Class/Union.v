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

Require Import ZF.Meta.Decl.Axiom.Union.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Small.

(* union P x <-> exists y, x :< y /\ P y.                                       *)
Definition union : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (And
            (Elem (Var 1) (Var 0))
            (App (Var 2) (Var 0))))
  |}.

(* forall P Q, equiv P Q -> equiv (union P) (union Q).                          *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "union") (args [Var 1])
          ; IdentT (Name.local "union") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P, Small P -> Small (union P).                                        *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 0]))
      (IdentT (Name.local "Small")
        (args [IdentT (Name.local "union") (args [Var 0])]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify ZF.Meta.Decl.Axiom.Union.exports
  ; Env.unqualify ZF.Meta.Decl.Class.Equiv.exports
  ; Env.unqualify ZF.Meta.Decl.Class.Small.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "union", union)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat", EquivCompat)
      ; (Name.local "IsSmall"    , IsSmall)
      ]
  ].

Definition env : Env := Env.union imports exports.
