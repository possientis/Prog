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
Require Import ZF.Meta.Decl.Class.Prod.
Require Import ZF.Meta.Decl.Class.Relation.Cmp.
Require Import ZF.Meta.Decl.Class.Relation.Converse.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.FunctionalAt.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Relation.Range.
Require Import ZF.Meta.Decl.Class.Relation.Relation.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.

(* compose G F is the relational composite of G after F.                        *)
Definition compose : DeclT :=
  {| paraT := [TyClass; TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (Ex
            (Ex
              (And
                (SyntaxT.Equal
                  (Var 3)
                  (IdentT (Name.local "ordPair") (args [Var 2; Var 0])))
                (And
                  (App
                    (Var 4)
                    (IdentT (Name.local "ordPair") (args [Var 2; Var 1])))
                  (App
                    (Var 5)
                    (IdentT (Name.local "ordPair") (args [Var 1; Var 0]))))))))
  |}.

(* forall F G x z, (G compose F)(x,z) iff some y links F then G.                *)
Definition Charac2 : DeclP :=
  let concl :=
    Iff
      (App
        (IdentT (Name.local "compose") (args [Var 2; Var 3]))
        (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
      (Ex
        (And
          (App
            (Var 4)
            (IdentT (Name.local "ordPair") (args [Var 2; Var 0])))
          (App
            (Var 3)
            (IdentT (Name.local "ordPair") (args [Var 0; Var 1])))))
  in
    {| paraP  := [TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F F' G G', equivalence of factors gives equivalence of composites.    *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "compose") (args [Var 1; Var 3])
            ; IdentT (Name.local "compose") (args [Var 0; Var 2])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G G', left equivalence compatibility of composition.                *)
Definition EquivCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "compose") (args [Var 1; Var 2])
          ; IdentT (Name.local "compose") (args [Var 0; Var 2])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F F' G, right equivalence compatibility of composition.               *)
Definition EquivCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "compose") (args [Var 0; Var 2])
          ; IdentT (Name.local "compose") (args [Var 0; Var 1])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G H, composition is associative.                                    *)
Definition Assoc : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "compose")
            (args [IdentT (Name.local "compose") (args [Var 0; Var 1]); Var 2])
        ; IdentT (Name.local "compose")
            (args [Var 0; IdentT (Name.local "compose") (args [Var 1; Var 2])])
        ])
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, the composite of two classes is a relation.                      *)
Definition IsRelation : DeclP :=
  let concl :=
    IdentT (Name.local "Relation")
      (args [IdentT (Name.local "compose") (args [Var 0; Var 1])])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, the composite of two functional classes is functional.           *)
Definition IsFunctional : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Functional") (args [Var 0]))
        (IdentT (Name.local "Functional")
          (args [IdentT (Name.local "compose") (args [Var 0; Var 1])])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, converse of a composite is the reversed composite of converses.  *)
Definition Converse : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "converse")
            (args [IdentT (Name.local "compose") (args [Var 0; Var 1])])
        ; IdentT (Name.local "compose")
            (args
              [ IdentT (Name.local "converse") (args [Var 1])
              ; IdentT (Name.local "converse") (args [Var 0])
              ])
        ])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, domain of the composite is included in domain F.                 *)
Definition DomainIsSmaller : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args
        [ IdentT (Name.local "domain")
            (args [IdentT (Name.local "compose") (args [Var 0; Var 1])])
        ; IdentT (Name.local "domain") (args [Var 1])
        ])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, range of the composite is included in range G.                   *)
Definition RangeIsSmaller : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args
        [ IdentT (Name.local "range")
            (args [IdentT (Name.local "compose") (args [Var 0; Var 1])])
        ; IdentT (Name.local "range") (args [Var 0])
        ])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, if range F is in domain G, composite domain equals domain F.     *)
Definition DomainIsSame : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl")
        (args [IdentT (Name.local "range") (args [Var 1]);
               IdentT (Name.local "domain") (args [Var 0])])
      )
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "domain")
              (args [IdentT (Name.local "compose") (args [Var 0; Var 1])])
          ; IdentT (Name.local "domain") (args [Var 1])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, for functional F, domain equality characterizes range-domain fit.*)
Definition DomainIsSame2 : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 1]))
      (Iff
        (IdentT (Name.local "Incl")
          (args [IdentT (Name.local "range") (args [Var 1]);
                 IdentT (Name.local "domain") (args [Var 0])]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "domain")
                (args [IdentT (Name.local "compose") (args [Var 0; Var 1])])
            ; IdentT (Name.local "domain") (args [Var 1])
            ])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, if domain G is in range F, composite range equals range G.       *)
Definition RangeIsSame : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl")
        (args [IdentT (Name.local "domain") (args [Var 0]);
               IdentT (Name.local "range") (args [Var 1])]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "range")
              (args [IdentT (Name.local "compose") (args [Var 0; Var 1])])
          ; IdentT (Name.local "range") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, for injective G, range equality characterizes domain-range fit.  *)
Definition RangeIsSame2 : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional")
        (args [IdentT (Name.local "converse") (args [Var 0])]))
      (Iff
        (IdentT (Name.local "Incl")
          (args [IdentT (Name.local "domain") (args [Var 0]);
                 IdentT (Name.local "range") (args [Var 1])]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "range")
                (args [IdentT (Name.local "compose") (args [Var 0; Var 1])])
            ; IdentT (Name.local "range") (args [Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G a, domain of G.F at a is domain F at a and domain G at F!a.       *)
Definition FunctionalAtDomainCharac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "FunctionalAt") (args [Var 2; Var 0]))
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

(* forall F G a, functional domain characterization of G.F.                     *)
Definition FunctionalDomainCharac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 2]))
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

(* forall F G a, pointwise functionality composes where the intermediate exists.*)
Definition IsFunctionalAt : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "FunctionalAt") (args [Var 2; Var 0]))
      (Imp
        (IdentT (Name.local "FunctionalAt")
          (args [Var 1; IdentT (Name.local "eval") (args [Var 2; Var 0])]))
        (Imp
          (App (IdentT (Name.local "domain") (args [Var 2])) (Var 0))
          (IdentT (Name.local "FunctionalAt")
            (args
              [ IdentT (Name.local "compose") (args [Var 1; Var 2])
              ; Var 0
              ]))))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G a, pointwise evaluation of a composite.                           *)
Definition FunctionalAtEval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "FunctionalAt") (args [Var 2; Var 0]))
      (Imp
        (IdentT (Name.local "FunctionalAt")
          (args [Var 1; IdentT (Name.local "eval") (args [Var 2; Var 0])]))
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

(* forall F G a, evaluation of a composite of functional classes.               *)
Definition Eval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 2]))
      (Imp
        (IdentT (Name.local "Functional") (args [Var 1]))
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

(* forall F G, the composite is included in the Cmp-image of F times G.         *)
Definition ImageUnderCmp : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args
        [ IdentT (Name.local "compose") (args [Var 0; Var 1])
        ; IdentT (Name.local "image")
            (args
              [ IdentT (Name.local "Cmp") (args [])
              ; IdentT (Name.local "prod") (args [Var 1; Var 0])
              ])
        ])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, the composite of two small classes is small.                     *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "compose") (args [Var 0; Var 1])])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A, image of A under G.F equals image of F[A] under G.             *)
Definition Image : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "image")
            (args [IdentT (Name.local "compose") (args [Var 1; Var 2]); Var 0])
        ; IdentT (Name.local "image")
            (args [Var 1; IdentT (Name.local "image") (args [Var 2; Var 0])])
        ])
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.
(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Prod.exports
  ; Env.unqualify Cmp.exports
  ; Env.unqualify Converse.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify FunctionalAt.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Range.exports
  ; Env.unqualify Relation.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify EvalOfClass.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "compose", compose)
      ]
  ; Env.fromListP
      [ (Name.local "Charac2"                 , Charac2)
      ; (Name.local "EquivCompat"              , EquivCompat)
      ; (Name.local "EquivCompatL"             , EquivCompatL)
      ; (Name.local "EquivCompatR"             , EquivCompatR)
      ; (Name.local "Assoc"                    , Assoc)
      ; (Name.local "IsRelation"               , IsRelation)
      ; (Name.local "IsFunctional"             , IsFunctional)
      ; (Name.local "Converse"                 , Converse)
      ; (Name.local "DomainIsSmaller"          , DomainIsSmaller)
      ; (Name.local "RangeIsSmaller"           , RangeIsSmaller)
      ; (Name.local "DomainIsSame"             , DomainIsSame)
      ; (Name.local "DomainIsSame2"            , DomainIsSame2)
      ; (Name.local "RangeIsSame"              , RangeIsSame)
      ; (Name.local "RangeIsSame2"             , RangeIsSame2)
      ; (Name.local "FunctionalAtDomainCharac" , FunctionalAtDomainCharac)
      ; (Name.local "FunctionalDomainCharac"   , FunctionalDomainCharac)
      ; (Name.local "IsFunctionalAt"           , IsFunctionalAt)
      ; (Name.local "FunctionalAtEval"         , FunctionalAtEval)
      ; (Name.local "Eval"                     , Eval)
      ; (Name.local "IsSmall"                  , IsSmall)
      ; (Name.local "Image"                    , Image)
      ]
  ].

Definition env : Env := Env.union imports exports.
