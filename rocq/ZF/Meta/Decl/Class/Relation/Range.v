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
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Relation.Snd.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* range F y <-> exists x, F :(x,y):.                                           *)
Definition range : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (App
            (Var 2)
            (IdentT (Name.local "ordPair") (args [Var 0; Var 1]))))
  |}.

(* forall F G, equiv F G -> equiv (range F) (range G).                          *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "range") (args [Var 1])
          ; IdentT (Name.local "range") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, Incl F G -> Incl (range F) (range G).                            *)
Definition InclCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "range") (args [Var 1])
          ; IdentT (Name.local "range") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, equiv (image Snd F) (range F).                                     *)
Definition ImageUnderSnd : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "image")
            (args [IdentT (Name.local "Snd") (args []); Var 0])
        ; IdentT (Name.local "range") (args [Var 0])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, equiv (image F (domain F)) (range F).                              *)
Definition ImageOfDomain : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "image")
            (args
              [ Var 0
              ; IdentT (Name.local "domain") (args [Var 0])
              ])
        ; IdentT (Name.local "range") (args [Var 0])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, Small F -> Small (range F).                                        *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 0]))
      (IdentT (Name.local "Small")
        (args [IdentT (Name.local "range") (args [Var 0])]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, not equiv (domain F) empty -> not equiv (range F) empty.           *)
Definition IsNotEmpty : DeclP :=
  let concl :=
    Imp
      (Not
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "domain") (args [Var 0])
            ; IdentT (Name.local "empty") (args [])
            ])))
      (Not
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "range") (args [Var 0])
            ; IdentT (Name.local "empty") (args [])
            ])))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, Incl (image F A) (range F).                                      *)
Definition ImageIncl : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args
        [ IdentT (Name.local "image") (args [Var 1; Var 0])
        ; IdentT (Name.local "range") (args [Var 1])
        ])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Empty.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Snd.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "range", range)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat" , EquivCompat)
      ; (Name.local "InclCompat"  , InclCompat)
      ; (Name.local "ImageUnderSnd", ImageUnderSnd)
      ; (Name.local "ImageOfDomain", ImageOfDomain)
      ; (Name.local "IsSmall"     , IsSmall)
      ; (Name.local "IsNotEmpty"  , IsNotEmpty)
      ; (Name.local "ImageIncl"   , ImageIncl)
      ]
  ].

Definition env : Env := Env.union imports exports.
