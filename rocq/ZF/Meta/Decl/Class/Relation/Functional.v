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
Require Import ZF.Meta.Decl.Class.Relation.FunctionalAt.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* Functional F <-> forall x y z, F :(x,y): -> F :(x,z): -> y = z.              *)
Definition Functional : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyProp
  ;  bodyT :=
      All
        (All
          (All
            (Imp
              (App (Var 3)
                (IdentT (Name.local "ordPair") (args [Var 2; Var 1])))
              (Imp
                (App (Var 3)
                  (IdentT (Name.local "ordPair") (args [Var 2; Var 0])))
                (SyntaxT.Equal (Var 1) (Var 0))))))
  |}.

(* forall F G, equiv F G -> Functional F -> Functional G.                       *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Functional") (args [Var 1]))
        (IdentT (Name.local "Functional") (args [Var 0])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, Incl F G -> Functional G -> Functional F.                        *)
Definition InclCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Functional") (args [Var 0]))
        (IdentT (Name.local "Functional") (args [Var 1])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, Functional F <-> forall a, FunctionalAt F a.                       *)
Definition IsFunctionalAt : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.local "Functional") (args [Var 0]))
      (All
        (IdentT (Name.local "FunctionalAt") (args [Var 1; Var 0])))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Incl.exports
  ; Env.unqualify FunctionalAt.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "Functional", Functional)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat"   , EquivCompat)
      ; (Name.local "InclCompat"    , InclCompat)
      ; (Name.local "IsFunctionalAt", IsFunctionalAt)
      ]
  ].

Definition env : Env := Env.union imports exports.
