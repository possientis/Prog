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
Require Import ZF.Meta.Decl.Class.Relation.Converse.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Relation.Range.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.

(* forall F P x, inverse image membership means some P-value is related by F.   *)
Definition Charac : DeclP :=
  let concl :=
    Iff
      (App
        (IdentT (Name.local "image")
          (args [IdentT (Name.local "converse") (args [Var 2]); Var 1]))
        (Var 0))
      (Ex
        (And
          (App (Var 2) (Var 0))
          (App
            (Var 3)
            (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G P Q, equivalent relation and target give equivalent inverse image.*)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "image")
                (args [IdentT (Name.local "converse") (args [Var 3]); Var 1])
            ; IdentT (Name.local "image")
                (args [IdentT (Name.local "converse") (args [Var 2]); Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G P, left equivalence compatibility of inverse image.               *)
Definition EquivCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "image")
              (args [IdentT (Name.local "converse") (args [Var 2]); Var 0])
          ; IdentT (Name.local "image")
              (args [IdentT (Name.local "converse") (args [Var 1]); Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F P Q, right equivalence compatibility of inverse image.              *)
Definition EquivCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "image")
              (args [IdentT (Name.local "converse") (args [Var 2]); Var 1])
          ; IdentT (Name.local "image")
              (args [IdentT (Name.local "converse") (args [Var 2]); Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G P Q, inclusion of relation and target gives inverse-image incl.   *)
Definition InclCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
        (IdentT (Name.local "Incl")
          (args
            [ IdentT (Name.local "image")
                (args [IdentT (Name.local "converse") (args [Var 3]); Var 1])
            ; IdentT (Name.local "image")
                (args [IdentT (Name.local "converse") (args [Var 2]); Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G P, left inclusion compatibility of inverse image.                 *)
Definition InclCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 1]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "image")
              (args [IdentT (Name.local "converse") (args [Var 2]); Var 0])
          ; IdentT (Name.local "image")
              (args [IdentT (Name.local "converse") (args [Var 1]); Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F P Q, right inclusion compatibility of inverse image.                *)
Definition InclCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "image")
              (args [IdentT (Name.local "converse") (args [Var 2]); Var 1])
          ; IdentT (Name.local "image")
              (args [IdentT (Name.local "converse") (args [Var 2]); Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, inverse image of the range is the domain.                          *)
Definition OfRange : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "image")
            (args
              [ IdentT (Name.local "converse") (args [Var 0])
              ; IdentT (Name.local "range") (args [Var 0])
              ])
        ; IdentT (Name.local "domain") (args [Var 0])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F B x, for functional F, inverse image is domain and B of F!x.        *)
Definition Eval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 1]))
      (All
        (Iff
          (App
            (IdentT (Name.local "image")
              (args [IdentT (Name.local "converse") (args [Var 2]); Var 1]))
            (Var 0))
          (And
            (App (IdentT (Name.local "domain") (args [Var 2])) (Var 0))
            (App
              (Var 1)
              (IdentT (Name.local "eval") (args [Var 2; Var 0]))))))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, injectivity makes preimage of image included in A.               *)
Definition OfImageIsLess : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional")
        (args [IdentT (Name.local "converse") (args [Var 1])]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "image")
              (args
                [ IdentT (Name.local "converse") (args [Var 1])
                ; IdentT (Name.local "image") (args [Var 1; Var 0])
                ])
          ; Var 0
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, domain inclusion puts A in the preimage of its image.            *)
Definition OfImageIsMore : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl")
        (args [Var 0; IdentT (Name.local "domain") (args [Var 1])]))
      (IdentT (Name.local "Incl")
        (args
          [ Var 0
          ; IdentT (Name.local "image")
              (args
                [ IdentT (Name.local "converse") (args [Var 1])
                ; IdentT (Name.local "image") (args [Var 1; Var 0])
                ])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F B, functional image of inverse image is included in B.              *)
Definition ImageIsLess : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 1]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "image")
              (args
                [ Var 1
                ; IdentT (Name.local "image")
                    (args [IdentT (Name.local "converse") (args [Var 1]); Var 0])
                ])
          ; Var 0
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F B, range inclusion puts B in image of its inverse image.            *)
Definition ImageIsMore : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl")
        (args [Var 0; IdentT (Name.local "range") (args [Var 1])]))
      (IdentT (Name.local "Incl")
        (args
          [ Var 0
          ; IdentT (Name.local "image")
              (args
                [ Var 1
                ; IdentT (Name.local "image")
                    (args [IdentT (Name.local "converse") (args [Var 1]); Var 0])
                ])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.
(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Converse.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Range.exports
  ; Env.unqualify EvalOfClass.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.fromListP
  [ (Name.local "Charac"       , Charac)
  ; (Name.local "EquivCompat"   , EquivCompat)
  ; (Name.local "EquivCompatL"  , EquivCompatL)
  ; (Name.local "EquivCompatR"  , EquivCompatR)
  ; (Name.local "InclCompat"    , InclCompat)
  ; (Name.local "InclCompatL"   , InclCompatL)
  ; (Name.local "InclCompatR"   , InclCompatR)
  ; (Name.local "OfRange"       , OfRange)
  ; (Name.local "Eval"          , Eval)
  ; (Name.local "OfImageIsLess" , OfImageIsLess)
  ; (Name.local "OfImageIsMore" , OfImageIsMore)
  ; (Name.local "ImageIsLess"   , ImageIsLess)
  ; (Name.local "ImageIsMore"   , ImageIsMore)
  ].

Definition env : Env := Env.union imports exports.
