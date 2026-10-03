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
Require Import ZF.Meta.Decl.Class.Relation.Compose.
Require Import ZF.Meta.Decl.Class.Relation.Converse.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Relation.InvImage.
Require Import ZF.Meta.Decl.Class.Relation.Range.
Require Import ZF.Meta.Decl.Class.Relation.Restrict.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.

(* OneToOne F means both F and its converse are functional.                     *)
Definition OneToOne : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyProp
  ;  bodyT :=
      And
        (IdentT (Name.local "Functional") (args [Var 0]))
        (IdentT (Name.local "Functional")
          (args [IdentT (Name.local "converse") (args [Var 0])]))
  |}.

(* forall F G, equivalence preserves the one-to-one property.                   *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "OneToOne") (args [Var 1]))
        (IdentT (Name.local "OneToOne") (args [Var 0])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F x y z, one-to-one gives uniqueness of the left coordinate.          *)
Definition CharacL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 3]))
      (Imp
        (App (Var 3) (IdentT (Name.local "ordPair") (args [Var 1; Var 2])))
        (Imp
          (App (Var 3) (IdentT (Name.local "ordPair") (args [Var 0; Var 2])))
          (SyntaxT.Equal (Var 1) (Var 0))))
  in
    {| paraP  := [TyClass; TySet; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F x y z, one-to-one gives uniqueness of the right coordinate.         *)
Definition CharacR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 3]))
      (Imp
        (App (Var 3) (IdentT (Name.local "ordPair") (args [Var 2; Var 1])))
        (Imp
          (App (Var 3) (IdentT (Name.local "ordPair") (args [Var 2; Var 0])))
          (SyntaxT.Equal (Var 1) (Var 0))))
  in
    {| paraP  := [TyClass; TySet; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, one-to-one maps small classes to small images.                   *)
Definition ImageIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "image") (args [Var 1; Var 0])])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F B, one-to-one maps small classes to small inverse images.           *)
Definition InvImageIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small")
          (args
            [ IdentT (Name.local "image")
                (args [IdentT (Name.local "converse") (args [Var 1]); Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F x1 x2 y1 y2, equality of one coordinate is equivalent to the other. *)
Definition CoordEquiv : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 4]))
      (Imp
        (App (Var 4) (IdentT (Name.local "ordPair") (args [Var 3; Var 1])))
        (Imp
          (App (Var 4) (IdentT (Name.local "ordPair") (args [Var 2; Var 0])))
          (Iff (SyntaxT.Equal (Var 3) (Var 2))
               (SyntaxT.Equal (Var 1) (Var 0)))))
  in
    {| paraP  := [TyClass; TySet; TySet; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, the converse of a one-to-one class is one-to-one.                  *)
Definition Converse : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 0]))
      (IdentT (Name.local "OneToOne")
        (args [IdentT (Name.local "converse") (args [Var 0])]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F a y, membership at a is equivalent to evaluation when one-to-one.   *)
Definition Eval' : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 2]))
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

(* forall F a y, a related to y implies F!a = y when F is one-to-one.           *)
Definition Eval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 2]))
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

(* forall F a, one-to-one functions satisfy their graph at F!a.                 *)
Definition Satisfies : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 1]))
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
      (IdentT (Name.local "OneToOne") (args [Var 1]))
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

(* forall F A, image membership is characterized by evaluation on the domain.   *)
Definition ImageCharac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 1]))
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

(* forall F b, converse evaluation at a range element lies in the domain.       *)
Definition ConverseEvalIsInDomain : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 1]))
      (Imp
        (App (IdentT (Name.local "range") (args [Var 1])) (Var 0))
        (App
          (IdentT (Name.local "domain") (args [Var 1]))
          (IdentT (Name.local "eval")
            (args [IdentT (Name.local "converse") (args [Var 1]); Var 0]))))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, the composite of one-to-one classes is one-to-one.               *)
Definition Compose : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 1]))
      (Imp
        (IdentT (Name.local "OneToOne") (args [Var 0]))
        (IdentT (Name.local "OneToOne")
          (args [IdentT (Name.local "compose") (args [Var 0; Var 1])])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F x, applying the converse to F!x returns x on the domain.            *)
Definition ConverseEvalOfEval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 1]))
      (Imp
        (App (IdentT (Name.local "domain") (args [Var 1])) (Var 0))
        (SyntaxT.Equal
          (IdentT (Name.local "eval")
            (args
              [ IdentT (Name.local "converse") (args [Var 1])
              ; IdentT (Name.local "eval") (args [Var 1; Var 0])
              ]))
          (Var 0)))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F y, applying F to the converse value returns y on the range.         *)
Definition EvalOfConverseEval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 1]))
      (Imp
        (App (IdentT (Name.local "range") (args [Var 1])) (Var 0))
        (SyntaxT.Equal
          (IdentT (Name.local "eval")
            (args
              [ Var 1
              ; IdentT (Name.local "eval")
                  (args [IdentT (Name.local "converse") (args [Var 1]); Var 0])
              ]))
          (Var 0)))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G a, domain of a composite is characterized by successive domains.  *)
Definition DomainOfCompose : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 2]))
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

(* forall F G a, evaluation of a composite of one-to-one classes.               *)
Definition ComposeEval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 2]))
      (Imp
        (IdentT (Name.local "OneToOne") (args [Var 1]))
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

(* forall F A, inverse image of image is A on the domain.                       *)
Definition InvImageOfImage : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Incl")
          (args [Var 0; IdentT (Name.local "domain") (args [Var 1])]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "image")
                (args
                  [ IdentT (Name.local "converse") (args [Var 1])
                  ; IdentT (Name.local "image") (args [Var 1; Var 0])
                  ])
            ; Var 0
            ])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F B, image of inverse image is B on the range.                        *)
Definition ImageOfInvImage : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Incl")
          (args [Var 0; IdentT (Name.local "range") (args [Var 1])]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "image")
                (args
                  [ Var 1
                  ; IdentT (Name.local "image")
                      (args [IdentT (Name.local "converse") (args [Var 1]); Var 0])
                  ])
            ; Var 0
            ])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F x y, one-to-one evaluation is injective on the domain.              *)
Definition EvalInjective : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 2]))
      (Imp
        (App (IdentT (Name.local "domain") (args [Var 2])) (Var 1))
        (Imp
          (App (IdentT (Name.local "domain") (args [Var 2])) (Var 0))
          (Imp
            (SyntaxT.Equal
              (IdentT (Name.local "eval") (args [Var 2; Var 1]))
              (IdentT (Name.local "eval") (args [Var 2; Var 0])))
            (SyntaxT.Equal (Var 1) (Var 0)))))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, a functional class injective on its domain is one-to-one.          *)
Definition WhenFunctional : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 0]))
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

(* forall F A a, F!a lies in F[A] iff a lies in A.                              *)
Definition EvalInImage : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 2]))
      (Imp
        (App (IdentT (Name.local "domain") (args [Var 2])) (Var 0))
        (Iff
          (App
            (IdentT (Name.local "image") (args [Var 2; Var 1]))
            (IdentT (Name.local "eval") (args [Var 2; Var 0])))
          (App (Var 1) (Var 0))))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, the restriction of a one-to-one class is one-to-one.             *)
Definition Restrict : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "OneToOne") (args [Var 1]))
      (IdentT (Name.local "OneToOne")
        (args [IdentT (Name.local "restrict") (args [Var 1; Var 0])]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.
(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Compose.exports
  ; Env.unqualify Converse.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify InvImage.exports
  ; Env.unqualify Range.exports
  ; Env.unqualify Restrict.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify OrdPair.exports
  ; Env.unqualify EvalOfClass.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "OneToOne", OneToOne)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat"            , EquivCompat)
      ; (Name.local "CharacL"                , CharacL)
      ; (Name.local "CharacR"                , CharacR)
      ; (Name.local "ImageIsSmall"           , ImageIsSmall)
      ; (Name.local "InvImageIsSmall"        , InvImageIsSmall)
      ; (Name.local "CoordEquiv"             , CoordEquiv)
      ; (Name.local "Converse"               , Converse)
      ; (Name.local "Eval'"                  , Eval')
      ; (Name.local "Eval"                   , Eval)
      ; (Name.local "Satisfies"              , Satisfies)
      ; (Name.local "IsInRange"              , IsInRange)
      ; (Name.local "ImageCharac"            , ImageCharac)
      ; (Name.local "ConverseEvalIsInDomain" , ConverseEvalIsInDomain)
      ; (Name.local "Compose"                , Compose)
      ; (Name.local "ConverseEvalOfEval"     , ConverseEvalOfEval)
      ; (Name.local "EvalOfConverseEval"     , EvalOfConverseEval)
      ; (Name.local "DomainOfCompose"        , DomainOfCompose)
      ; (Name.local "ComposeEval"            , ComposeEval)
      ; (Name.local "InvImageOfImage"        , InvImageOfImage)
      ; (Name.local "ImageOfInvImage"        , ImageOfInvImage)
      ; (Name.local "EvalInjective"          , EvalInjective)
      ; (Name.local "WhenFunctional"         , WhenFunctional)
      ; (Name.local "EvalInImage"            , EvalInImage)
      ; (Name.local "Restrict"               , Restrict)
      ]
  ].

Definition env : Env := Env.union imports exports.
