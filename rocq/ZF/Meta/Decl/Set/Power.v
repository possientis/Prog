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

Require Import ZF.Meta.Decl.Class.Power.
Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.Incl.
Require Import ZF.Meta.Decl.Set.Single.

(* power a : U.                                                                 *)
Definition power : DeclT :=
  {| paraT := [TySet]
  ;  resT  := TySet
  ;  bodyT :=
      FromC
        (IdentT (Name.qualified "CPW" "power") (args [Var 0]))
  |}.

(* forall a x, x :< power a <-> Incl x a.                                       *)
Definition Charac : DeclP :=
  let concl :=
    All
      (Iff
        (Elem (Var 0) (IdentT (Name.local "power") (args [Var 1])))
        (IdentT (Name.local "Incl") (args [Var 0; Var 1])))
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a, a :< power a.                                                      *)
Definition IsIn : DeclP :=
  let concl :=
    Elem (Var 0) (IdentT (Name.local "power") (args [Var 0]))
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* power empty = single empty.                                                  *)
Definition WhenZero : DeclP :=
  let concl :=
    SyntaxT.Equal
      (IdentT (Name.local "power")
        (args [IdentT (Name.local "empty") (args [])]))
      (IdentT (Name.local "single")
        (args [IdentT (Name.local "empty") (args [])]))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.qualifyAs "CPW" Power.exports
  ; Env.unqualify Empty.exports
  ; Env.unqualify Incl.exports
  ; Env.unqualify Single.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "power", power)
      ]
  ; Env.fromListP
      [ (Name.local "Charac"  , Charac)
      ; (Name.local "IsIn"    , IsIn)
      ; (Name.local "WhenZero", WhenZero)
      ]
  ].

Definition env : Env := Env.union imports exports.
