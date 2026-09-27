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
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.FunctionalAt.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* IsValueAt F a y <-> F :(a,y): /\ FunctionalAt F a.                           *)
Definition IsValueAt : DeclT :=
  {| paraT := [TyClass; TySet; TySet]
  ;  resT  := TyProp
  ;  bodyT :=
      And
        (App
          (Var 2)
          (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
        (IdentT (Name.local "FunctionalAt") (args [Var 2; Var 1]))
  |}.

(* forall F G a y, F ~ G -> IsValueAt F a y -> IsValueAt G a y.                 *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "IsValueAt") (args [Var 3; Var 1; Var 0]))
        (IdentT (Name.local "IsValueAt") (args [Var 2; Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a y, FunctionalAt F a -> IsValueAt F a y <-> F :(a,y):.             *)
Definition WhenFunctionalAt : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "FunctionalAt") (args [Var 2; Var 1]))
      (Iff
        (IdentT (Name.local "IsValueAt") (args [Var 2; Var 1; Var 0]))
        (App
          (Var 2)
          (IdentT (Name.local "ordPair") (args [Var 1; Var 0]))))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a y, Functional F -> IsValueAt F a y <-> F :(a,y):.                 *)
Definition WhenFunctional : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 2]))
      (Iff
        (IdentT (Name.local "IsValueAt") (args [Var 2; Var 1; Var 0]))
        (App
          (Var 2)
          (IdentT (Name.local "ordPair") (args [Var 1; Var 0]))))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify FunctionalAt.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "IsValueAt", IsValueAt)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat"     , EquivCompat)
      ; (Name.local "WhenFunctionalAt", WhenFunctionalAt)
      ; (Name.local "WhenFunctional"  , WhenFunctional)
      ]
  ].

Definition env : Env := Env.union imports exports.
