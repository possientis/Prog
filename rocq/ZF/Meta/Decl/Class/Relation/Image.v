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

Require Import ZF.Meta.Decl.Axiom.Replacement.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* image F A y <-> exists x, A x /\ F :(x,y):.                                  *)
Definition image : DeclT :=
  {| paraT := [TyClass; TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (And
            (App (Var 2) (Var 0))
            (App (Var 3)
              (IdentT (Name.local "ordPair") (args [Var 0; Var 1])))))
  |}.

(* forall P Q R S, equiv P Q -> equiv R S -> equiv (image P R) (image Q S).     *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
        (IdentT (Name.local "equiv")
          (args [IdentT (Name.local "image") (args [Var 3; Var 1]);
           IdentT (Name.local "image") (args [Var 2; Var 0])])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> equiv (image P R) (image Q R).                    *)
Definition EquivCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (IdentT (Name.local "equiv")
        (args [IdentT (Name.local "image") (args [Var 2; Var 0]);
         IdentT (Name.local "image") (args [Var 1; Var 0])]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, equiv P Q -> equiv (image R P) (image R Q).                    *)
Definition EquivCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (IdentT (Name.local "equiv")
        (args [IdentT (Name.local "image") (args [Var 0; Var 2]);
         IdentT (Name.local "image") (args [Var 0; Var 1])]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R S, Incl P Q -> Incl R S -> Incl (image P R) (image Q S).        *)
Definition InclCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
        (IdentT (Name.local "Incl")
          (args [IdentT (Name.local "image") (args [Var 3; Var 1]);
           IdentT (Name.local "image") (args [Var 2; Var 0])])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, Incl P Q -> Incl (image P R) (image Q R).                      *)
Definition InclCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 1]))
      (IdentT (Name.local "Incl")
        (args [IdentT (Name.local "image") (args [Var 2; Var 0]);
         IdentT (Name.local "image") (args [Var 1; Var 0])]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall P Q R, Incl P Q -> Incl (image R P) (image R Q).                      *)
Definition InclCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 1]))
      (IdentT (Name.local "Incl")
        (args [IdentT (Name.local "image") (args [Var 0; Var 2]);
         IdentT (Name.local "image") (args [Var 0; Var 1])]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F P, Functional F -> Small P -> Small (image F P).                    *)
Definition IsSmallR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "image") (args [Var 1; Var 0])])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F P, Small F -> Small (image F P).                                    *)
Definition IsSmallL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 1]))
      (IdentT (Name.local "Small")
        (args [IdentT (Name.local "image") (args [Var 1; Var 0])]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Replacement.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Incl.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "image", image)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat" , EquivCompat)
      ; (Name.local "EquivCompatL", EquivCompatL)
      ; (Name.local "EquivCompatR", EquivCompatR)
      ; (Name.local "InclCompat"  , InclCompat)
      ; (Name.local "InclCompatL" , InclCompatL)
      ; (Name.local "InclCompatR" , InclCompatR)
      ; (Name.local "IsSmallR"    , IsSmallR)
      ; (Name.local "IsSmallL"    , IsSmallL)
      ]
  ].

Definition env : Env := Env.union imports exports.
