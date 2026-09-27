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

Require Import ZF.Meta.Decl.Class.Empty.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Relation.Fst.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* domain F x <-> exists y, F :(x,y):.                                          *)
Definition domain : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (App
            (Var 2)
            (IdentT (Name.local "ordPair") (args [Var 1; Var 0]))))
  |}.

(* forall F G, equiv F G -> equiv (domain F) (domain G).                        *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "domain") (args [Var 1])
          ; IdentT (Name.local "domain") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, Incl F G -> Incl (domain F) (domain G).                          *)
Definition InclCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "domain") (args [Var 1])
          ; IdentT (Name.local "domain") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, equiv (image Fst F) (domain F).                                    *)
Definition ImageUnderFst : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "image")
            (args [IdentT (Name.local "Fst") (args []); Var 0])
        ; IdentT (Name.local "domain") (args [Var 0])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, Small F -> Small (domain F).                                       *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 0]))
      (IdentT (Name.local "Small")
        (args [IdentT (Name.local "domain") (args [Var 0])]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, equiv F empty -> equiv (domain F) empty.                           *)
Definition WhenZero : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv")
        (args [Var 0; IdentT (Name.local "empty") (args [])]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "domain") (args [Var 0])
          ; IdentT (Name.local "empty") (args [])
          ]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Empty.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Fst.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "domain", domain)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat" , EquivCompat)
      ; (Name.local "InclCompat"  , InclCompat)
      ; (Name.local "ImageUnderFst", ImageUnderFst)
      ; (Name.local "IsSmall"     , IsSmall)
      ; (Name.local "WhenZero"    , WhenZero)
      ]
  ].

Definition env : Env := Env.union imports exports.
