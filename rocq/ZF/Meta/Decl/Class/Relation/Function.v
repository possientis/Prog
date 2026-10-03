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
Require Import ZF.Meta.Decl.Class.Inter2.
Require Import ZF.Meta.Decl.Class.Relation.Compose.
Require Import ZF.Meta.Decl.Class.Relation.Converse.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Relation.InvImage.
Require Import ZF.Meta.Decl.Class.Relation.OneToOne.
Require Import ZF.Meta.Decl.Class.Relation.Range.
Require Import ZF.Meta.Decl.Class.Relation.Relation.
Require Import ZF.Meta.Decl.Class.Relation.Restrict.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.
Require Import ZF.Meta.Decl.Set.Relation.ImageUnderClass.

(* Function F means F is a relation and is functional.                          *)
Definition Function : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyProp
  ;  bodyT :=
      And
        (IdentT (Name.local "Relation") (args [Var 0]))
        (IdentT (Name.local "Functional") (args [Var 0]))
  |}.

(* forall F G, equivalence preserves the function property.                     *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Function") (args [Var 1]))
        (IdentT (Name.local "Function") (args [Var 0])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, injectivity on the domain makes a function one-to-one.             *)
Definition IsOneToOne : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 0]))
      (Imp
        (All
          (All
            (Imp
              (App (IdentT (Name.local "domain") (args [Var 2])) (Var 1))
              (Imp
                (App (IdentT (Name.local "domain") (args [Var 2])) (Var 0))
                (Imp
                  (SyntaxT.Equal
                    (IdentT (Name.local "eval") (args [Var 2; Var 1]))
                    (IdentT (Name.local "eval") (args [Var 2; Var 0])))
                  (SyntaxT.Equal (Var 1) (Var 0)))))))
        (IdentT (Name.local "OneToOne") (args [Var 0])))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, functions are equal iff their domains and values agree.          *)
Definition Equal' : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Function") (args [Var 0]))
        (Iff
          (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
          (And
            (IdentT (Name.local "equiv")
              (args
                [ IdentT (Name.local "domain") (args [Var 1])
                ; IdentT (Name.local "domain") (args [Var 0])
                ]))
            (All
              (Imp
                (App (IdentT (Name.local "domain") (args [Var 2])) (Var 0))
                (SyntaxT.Equal
                  (IdentT (Name.local "eval") (args [Var 2; Var 0]))
                  (IdentT (Name.local "eval") (args [Var 1; Var 0]))))))))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, equal domains and pointwise equality give equal functions.       *)
Definition Equal : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Function") (args [Var 0]))
        (Imp
          (IdentT (Name.local "equiv")
            (args
              [ IdentT (Name.local "domain") (args [Var 1])
              ; IdentT (Name.local "domain") (args [Var 0])
              ]))
          (Imp
            (All
              (Imp
                (App (IdentT (Name.local "domain") (args [Var 2])) (Var 0))
                (SyntaxT.Equal
                  (IdentT (Name.local "eval") (args [Var 2; Var 0]))
                  (IdentT (Name.local "eval") (args [Var 1; Var 0])))))
            (IdentT (Name.local "equiv") (args [Var 1; Var 0])))))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, the image of the domain is the range.                              *)
Definition ImageOfDomain : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "image")
            (args [Var 0; IdentT (Name.local "domain") (args [Var 0])])
        ; IdentT (Name.local "range") (args [Var 0])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, functions take small classes to small images.                    *)
Definition ImageIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "image") (args [Var 1; Var 0])])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, a function with a small domain is small.                           *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 0]))
      (Imp
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "domain") (args [Var 0])]))
        (IdentT (Name.local "Small") (args [Var 0])))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, the inverse image of the range is the domain.                      *)
Definition InvImageOfRange : DeclP :=
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

(* forall F, a function with small domain has small range.                      *)
Definition RangeIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 0]))
      (Imp
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "domain") (args [Var 0])]))
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "range") (args [Var 0])])))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, one-to-one classes with small range have small domain.             *)
Definition DomainIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 0]))
      (Imp
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "range") (args [Var 0])]))
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "domain") (args [Var 0])])))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, the composite of two functional classes is a function.           *)
Definition FunctionalCompose : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Functional") (args [Var 0]))
        (IdentT (Name.local "Function")
          (args [IdentT (Name.local "compose") (args [Var 0; Var 1])])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, the composite of two function classes is a function.             *)
Definition Compose : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Function") (args [Var 0]))
        (IdentT (Name.local "Function")
          (args [IdentT (Name.local "compose") (args [Var 0; Var 1])])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a y, membership is equivalent to evaluation for functions.          *)
Definition Eval' : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 2]))
      (Imp
        (App (IdentT (Name.local "domain") (args [Var 2])) (Var 1))
        (Iff
          (App (Var 2) (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
          (SyntaxT.Equal
            (IdentT (Name.local "eval") (args [Var 2; Var 1]))
            (Var 0))))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a y, membership in a function gives the evaluated value.            *)
Definition Eval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 2]))
      (Imp
        (App (Var 2) (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
        (SyntaxT.Equal
          (IdentT (Name.local "eval") (args [Var 2; Var 1]))
          (Var 0)))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, a function satisfies its graph at F!a on its domain.             *)
Definition Satisfies : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 1]))
      (Imp
        (App (IdentT (Name.local "domain") (args [Var 1])) (Var 0))
        (App (Var 1)
          (IdentT (Name.local "ordPair")
            (args [Var 0; IdentT (Name.local "eval") (args [Var 1; Var 0])]))))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a, the value at a domain element lies in the range.                 *)
Definition IsInRange : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 1]))
      (Imp
        (App (IdentT (Name.local "domain") (args [Var 1])) (Var 0))
        (App
          (IdentT (Name.local "range") (args [Var 1]))
          (IdentT (Name.local "eval") (args [Var 1; Var 0]))))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A y, function image membership is characterized by evaluation.      *)
Definition ImageCharac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 1]))
      (All
        (Iff
          (App (IdentT (Name.local "image") (args [Var 2; Var 1])) (Var 0))
          (Ex
            (And
              (App (Var 2) (Var 0))
              (And
                (App (IdentT (Name.local "domain") (args [Var 3])) (Var 0))
                (SyntaxT.Equal
                  (IdentT (Name.local "eval") (args [Var 3; Var 0]))
                  (Var 1)))))))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a y, set image membership is characterized by evaluation.           *)
Definition ImageSetCharac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 1]))
      (All
        (Iff
          (Elem
            (Var 0)
            (IdentT (Name.qualified "SIM" "image") (args [Var 2; Var 1])))
          (Ex
            (And
              (Elem (Var 0) (Var 2))
              (And
                (App (IdentT (Name.local "domain") (args [Var 3])) (Var 0))
                (SyntaxT.Equal
                  (IdentT (Name.local "eval") (args [Var 3; Var 0]))
                  (Var 1)))))))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G a, domain of G.F is characterized by successive domains.          *)
Definition DomainOfCompose : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 2]))
      (Iff
        (App
          (IdentT (Name.local "domain")
            (args [IdentT (Name.local "compose") (args [Var 1; Var 2])]))
          (Var 0))
        (And
          (App (IdentT (Name.local "domain") (args [Var 2])) (Var 0))
          (App
            (IdentT (Name.local "domain") (args [Var 1]))
            (IdentT (Name.local "eval") (args [Var 2; Var 0])))))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G a, evaluation of a composite of function classes.                 *)
Definition ComposeEval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 2]))
      (Imp
        (IdentT (Name.local "Function") (args [Var 1]))
        (Imp
          (App (IdentT (Name.local "domain") (args [Var 2])) (Var 0))
          (Imp
            (App
              (IdentT (Name.local "domain") (args [Var 1]))
              (IdentT (Name.local "eval") (args [Var 2; Var 0])))
            (SyntaxT.Equal
              (IdentT (Name.local "eval")
                (args
                  [ IdentT (Name.local "compose") (args [Var 1; Var 2])
                  ; Var 0
                  ]))
              (IdentT (Name.local "eval")
                (args
                  [ Var 1
                  ; IdentT (Name.local "eval") (args [Var 2; Var 0])
                  ]))))))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F y, range membership is characterized by evaluation.                 *)
Definition RangeCharac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 1]))
      (Iff
        (App (IdentT (Name.local "range") (args [Var 1])) (Var 0))
        (Ex
          (And
            (App (IdentT (Name.local "domain") (args [Var 2])) (Var 0))
            (SyntaxT.Equal
              (IdentT (Name.local "eval") (args [Var 2; Var 0]))
              (Var 1)))))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, a nonempty domain gives a nonempty range.                          *)
Definition RangeIsNotEmpty : DeclP :=
  let concl :=
    Imp
      (Not
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "domain") (args [Var 0])
            ; IdentT (Name.qualified "CEM" "empty") (args [])
            ])))
      (Not
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "range") (args [Var 0])
            ; IdentT (Name.qualified "CEM" "empty") (args [])
            ])))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, a function equals its restriction to its domain.                   *)
Definition IsRestrict : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ Var 0
          ; IdentT (Name.local "restrict")
              (args [Var 0; IdentT (Name.local "domain") (args [Var 0])])
          ]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, restricting a function gives a function.                         *)
Definition Restrict : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 1]))
      (IdentT (Name.local "Function")
        (args [IdentT (Name.local "restrict") (args [Var 1; Var 0])]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A, pointwise agreement on A gives equal restrictions to A.        *)
Definition RestrictEqual : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Function") (args [Var 2]))
      (Imp
        (IdentT (Name.local "Function") (args [Var 1]))
        (Imp
          (IdentT (Name.local "Incl")
            (args [Var 0; IdentT (Name.local "domain") (args [Var 2])]))
          (Imp
            (IdentT (Name.local "Incl")
              (args [Var 0; IdentT (Name.local "domain") (args [Var 1])]))
            (Imp
              (All
                (Imp
                  (App (Var 1) (Var 0))
                  (SyntaxT.Equal
                    (IdentT (Name.local "eval") (args [Var 3; Var 0]))
                    (IdentT (Name.local "eval") (args [Var 2; Var 0])))))
              (IdentT (Name.local "equiv")
                (args
                  [ IdentT (Name.local "restrict") (args [Var 2; Var 0])
                  ; IdentT (Name.local "restrict") (args [Var 1; Var 0])
                  ]))))))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Inter2.exports
  ; Env.unqualify Compose.exports
  ; Env.unqualify Converse.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify InvImage.exports
  ; Env.unqualify OneToOne.exports
  ; Env.unqualify Range.exports
  ; Env.unqualify Relation.exports
  ; Env.unqualify Restrict.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify OrdPair.exports
  ; Env.unqualify EvalOfClass.exports
  ; Env.qualifyAs "SIM" ImageUnderClass.exports
  ; Env.qualifyAs "CEM" Class.Empty.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "Function", Function)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat"     , EquivCompat)
      ; (Name.local "IsOneToOne"      , IsOneToOne)
      ; (Name.local "Equal'"          , Equal')
      ; (Name.local "Equal"           , Equal)
      ; (Name.local "ImageOfDomain"   , ImageOfDomain)
      ; (Name.local "ImageIsSmall"    , ImageIsSmall)
      ; (Name.local "IsSmall"         , IsSmall)
      ; (Name.local "InvImageOfRange" , InvImageOfRange)
      ; (Name.local "RangeIsSmall"    , RangeIsSmall)
      ; (Name.local "DomainIsSmall"   , DomainIsSmall)
      ; (Name.local "FunctionalCompose", FunctionalCompose)
      ; (Name.local "Compose"         , Compose)
      ; (Name.local "Eval'"           , Eval')
      ; (Name.local "Eval"            , Eval)
      ; (Name.local "Satisfies"       , Satisfies)
      ; (Name.local "IsInRange"       , IsInRange)
      ; (Name.local "ImageCharac"     , ImageCharac)
      ; (Name.local "ImageSetCharac"  , ImageSetCharac)
      ; (Name.local "DomainOfCompose" , DomainOfCompose)
      ; (Name.local "ComposeEval"     , ComposeEval)
      ; (Name.local "RangeCharac"     , RangeCharac)
      ; (Name.local "RangeIsNotEmpty" , RangeIsNotEmpty)
      ; (Name.local "IsRestrict"      , IsRestrict)
      ; (Name.local "Restrict"        , Restrict)
      ; (Name.local "RestrictEqual"   , RestrictEqual)
      ]
  ].

Definition env : Env := Env.union imports exports.
