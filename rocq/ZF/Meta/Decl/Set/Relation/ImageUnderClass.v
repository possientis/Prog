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

Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.Incl.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.
Require Import ZF.Meta.Decl.Set.Truncate.

(* image F a := truncate (class-image F (toClass a)).                           *)
Definition image : DeclT :=
  {| paraT := [TyClass; TySet]
  ;  resT  := TySet
  ;  bodyT :=
      IdentT (Name.local "truncate")
        (args
          [ IdentT (Name.qualified "CIMG" "image")
              (args [Var 1; IdentT (Name.local "toClass") (args [Var 0])])
          ])
  |}.

(* forall F a, Functional F -> toClass (image F a) is class-image F a.          *)
Definition ToClass : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 1]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "toClass")
              (args [IdentT (Name.local "image") (args [Var 1; Var 0])])
          ; IdentT (Name.qualified "CIMG" "image")
              (args [Var 1; IdentT (Name.local "toClass") (args [Var 0])])
          ]))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, Small F -> toClass (image F a) is class-image F a.               *)
Definition ToClassWhenSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 1]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "toClass")
              (args [IdentT (Name.local "image") (args [Var 1; Var 0])])
          ; IdentT (Name.qualified "CIMG" "image")
              (args [Var 1; IdentT (Name.local "toClass") (args [Var 0])])
          ]))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a y, functionality and image membership give a preimage.            *)
Definition Charac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 2]))
      (Imp
        (Elem (Var 0) (IdentT (Name.local "image") (args [Var 2; Var 1])))
        (Ex
          (And
            (Elem (Var 0) (Var 2))
            (App
              (Var 3)
              (IdentT (Name.local "ordPair") (args [Var 0; Var 1]))))))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a x y, a mapped element belongs to the image.                       *)
Definition CharacRev : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 3]))
      (Imp
        (Elem (Var 1) (Var 2))
        (Imp
          (App
            (Var 3)
            (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
          (Elem
            (Var 0)
            (IdentT (Name.local "image") (args [Var 3; Var 2])))))
  in
    {| paraP  := [TyClass; TySet; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G a, equivalent classes have equal set images.                      *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (SyntaxT.Equal
        (IdentT (Name.local "image") (args [Var 2; Var 0]))
        (IdentT (Name.local "image") (args [Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G a b, compatible function and set inclusions include images.       *)
Definition InclCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 2]))
      (Imp
        (IdentT (Name.qualified "CIN" "Incl") (args [Var 3; Var 2]))
        (Imp
          (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
          (IdentT (Name.local "Incl")
            (args
              [ IdentT (Name.local "image") (args [Var 3; Var 1])
              ; IdentT (Name.local "image") (args [Var 2; Var 0])
              ]))))
  in
    {| paraP  := [TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G a, left inclusion compatibility of set image.                     *)
Definition InclCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 1]))
      (Imp
        (IdentT (Name.qualified "CIN" "Incl") (args [Var 2; Var 1]))
        (IdentT (Name.local "Incl")
          (args
            [ IdentT (Name.local "image") (args [Var 2; Var 0])
            ; IdentT (Name.local "image") (args [Var 1; Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a b, right inclusion compatibility of set image.                    *)
Definition InclCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 2]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
        (IdentT (Name.local "Incl")
          (args
            [ IdentT (Name.local "image") (args [Var 2; Var 1])
            ; IdentT (Name.local "image") (args [Var 2; Var 0])
            ])))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, a = empty -> image F a = empty.                                  *)
Definition WhenZero : DeclP :=
  let concl :=
    Imp
      (SyntaxT.Equal (Var 0) (IdentT (Name.local "empty") (args [])))
      (SyntaxT.Equal
        (IdentT (Name.local "image") (args [Var 1; Var 0]))
        (IdentT (Name.local "empty") (args [])))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a x, if F is functional and x is in a domain, F!x is in F[a].       *)
Definition IsIn : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 2]))
      (Imp
        (App (IdentT (Name.local "domain") (args [Var 2])) (Var 0))
        (Imp
          (Elem (Var 0) (Var 1))
          (Elem
            (IdentT (Name.local "eval") (args [Var 2; Var 0]))
            (IdentT (Name.local "image") (args [Var 2; Var 1])))))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.qualifyAs "CIN" Class.Incl.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Functional.exports
  ; Env.qualifyAs "CIMG" Image.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify Empty.exports
  ; Env.unqualify Incl.exports
  ; Env.unqualify OrdPair.exports
  ; Env.unqualify EvalOfClass.exports
  ; Env.unqualify Truncate.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "image", image)
      ]
  ; Env.fromListP
      [ (Name.local "ToClass"         , ToClass)
      ; (Name.local "ToClassWhenSmall", ToClassWhenSmall)
      ; (Name.local "Charac"          , Charac)
      ; (Name.local "CharacRev"       , CharacRev)
      ; (Name.local "EquivCompat"     , EquivCompat)
      ; (Name.local "InclCompat"      , InclCompat)
      ; (Name.local "InclCompatL"     , InclCompatL)
      ; (Name.local "InclCompatR"     , InclCompatR)
      ; (Name.local "WhenZero"        , WhenZero)
      ; (Name.local "IsIn"            , IsIn)
      ]
  ].

Definition env : Env := Env.union imports exports.
